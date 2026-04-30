module
public meta import Lean
public meta import Lean.Elab.SyntheticMVars
public meta import Reap.PremiseSelection.API
public meta import Reap.Tactic.WallClock
public meta import TreeSearch.BestFirst
public meta import TreeSearch.MCTS
open Lean Meta Elab Tactic TreeSearch
open Reap.WallClock

public meta section

namespace Reap.TreeSearch

register_option reap.heartbeats : Nat := {
  defValue := 1000000000
  descr := "Maximum heartbeats per tactic"
}

def withHeartbeats {α : Type _} (heartbeats : Nat) (x : TacticM α) : TacticM α :=
  Core.withCurrHeartbeats <| withTheReader Core.Context (fun s => { s with maxHeartbeats := heartbeats }) x

def evalTacticStr (str : String) (heartbeats : Nat) : TacticM (Option Tactic.SavedState) := do
  withCumulativeWallClockTime "reap.wall.tactic_eval" do
    let .ok stx := Parser.runParserCategory (← getEnv) `tactic str | return none
    let savedState ← Tactic.saveState
    let savedMessages := (← getThe Core.State).messages
    modifyThe Core.State fun st => { st with messages := {} }
    try
      let success ← tryCatchRuntimeEx (handler := fun _ => return false) do
        withHeartbeats heartbeats <| do
          evalTactic stx
          Term.synthesizeSyntheticMVarsNoPostponing
          pruneSolvedGoals
        return true
      if success then
        if (← getThe Core.State).messages.hasErrors then
          savedState.restore
          modifyThe Core.State fun st => { st with messages := savedMessages }
          return none
      else
        savedState.restore
        modifyThe Core.State fun st => { st with messages := savedMessages }
        return none
    catch _ =>
      savedState.restore
      modifyThe Core.State fun st => { st with messages := savedMessages }
      return none
    modifyThe Core.State fun st => { st with messages := savedMessages }
    return ← Tactic.saveState

def communicate (obj : Json) : IO Unit :=
  -- HACK: communicate the search tree to parent process in an unnecessarily complicated way
  -- since Lean devs think they are so smart, and we (other devs) don't know what we want
  try
    IO.FS.withFile "/dev/fd/3" .write fun h =>
      h.putStrLn obj.compress
  catch _ => return ()

def getGoalTypes (ss : Tactic.SavedState) : TacticM (Option (Array Expr)) := do
  ss.restore
  let goals ← getUnsolvedGoals
  let mut goalTypes := #[]
  for g in goals do
    let t ← g.getTypeCleanup
    if t.hasExprMVar then
      return none
    else
      goalTypes := goalTypes.push t
  return some goalTypes

def unifyTypes (t₁ t₂ : Array Expr) : TacticM Bool := do
  let mut ret := true
  let mut t₂' := t₂
  for t in t₁ do
    if let some i ← t₂'.findIdxM? fun t' => Meta.isDefEqGuarded t t' then
      t₂' := t₂'.eraseIdx! i
    else
      ret := false
      break
  return ret

def isSolved (ss : Tactic.SavedState) : TacticM Bool := do
  ss.restore
  return (← getUnsolvedGoals).isEmpty

abbrev TacGen := List MVarId → MetaM (Array (String × Array PremiseSelectionResult × Float))
/-- AlphaProof-style state value V(s): a negative estimate of the remaining
proof length from the current tactic state. -/
abbrev StateEval := List MVarId → MetaM Float

structure SearchState where
  state : Tactic.SavedState
  score : Float
  visitCount : Nat := 0

inductive NodeData where
  | error (message : String)
  | ok (data : SearchState)

namespace NodeData
def priority : NodeData → TacticM Float
  | .error _ => return Float.inf
  | .ok data => do
      if ← isSolved data.state then
        return Float.inf
      else
        return data.score

def visitCount : NodeData → Nat
  | .error _ => 0
  | .ok data => data.visitCount

def isTerminal : NodeData → TacticM Bool
  | .error _ => pure false
  | .ok data => TreeSearch.isSolved data.state

def restore : NodeData → TacticM Unit
  | .error _ => pure ()
  | .ok data => data.state.restore

end NodeData

def ppNodeData : NodeData → TacticM Json
  | .error message => pure <| json%{ message: $message }
  | .ok data => do
    data.state.restore
    let pp ← (← getUnsolvedGoals).mapM fun g => do return toString (← Meta.ppGoal g)
    return json%{
      state: $(pp),
      score: $(data.score),
      visitCount: $(data.visitCount)
    }

def ppNode {ε} [ToJson ε] (node : Node NodeData ε) : TacticM Json := do
  return json%{
    data: $(← ppNodeData node.data),
    children: $(node.children)
  }

namespace BFS
def expand (tg : TacGen) (se : Option StateEval) : NodeData → TacticM (Array (String × NodeData))
  | .error _ => pure #[]
  | .ok data => do
    let state := data.state
    let score := data.score
    state.restore
    let tactics ← tg (← getUnsolvedGoals)
    tactics.mapM fun (t, _, Δp) => do
      state.restore
      if let some s' ← evalTacticStr t (reap.heartbeats.get (← getOptions)) then
        -- TODO: merge nodes
        s'.restore
        let g ← getUnsolvedGoals
        let p' ← if g.isEmpty then
          pure Float.inf
        else if let some se := se then
          se g
        else
          pure (score + Δp)
        return (t, .ok ⟨s', p', 0⟩)
      else
        return (t, .error "")

/--
TODO: For now, `proofSearchBFS` is exposed to the root namespace
so that we don't need to make any changes in the reap repository.
In the future, we may want to move it to a more appropriate namespace.
-/
def proofSearchBFS (tg : TacGen) (se : Option StateEval)
    (maxNodes := BestFirst.defaultMaxNodes) : TacticM Unit := do
  withCumulativeWallClockTime "reap.wall.bfs.total" do
    let (k, nodes) ← bestFirstSearch NodeData.priority NodeData.isTerminal
      (expand tg se) (.ok ⟨(← Tactic.saveState), 0.0, 0⟩) maxNodes
    let ppNodes ← nodes.mapM ppNode
    let info := json%{
      solution : $k,
      nodes : $ppNodes
    }
    communicate info

    if let some k := k then
      let some {data := .ok data, ..} := nodes[k]? | unreachable!
      data.state.restore
  printCumulativeWallClockTimes

end BFS

namespace MCTS

structure EdgeData where
  tacticStr : String
  premise : Array PremiseSelectionResult
  prior : Float
  totalValue : Float := 0.0   -- Sum of backed-up edge values V(s,a)
  visitCount : Nat := 0       -- N(s,a): visit count
  exhausted : Bool := false   -- this tactic/edge is confirmed invalid
deriving ToJson

abbrev NodeType := Node NodeData (EdgeData × NodeData)

structure CheckedChild where
  tacticStr : String
  premise : Array PremiseSelectionResult
  prior : Float
  state : Tactic.SavedState
  score : Float

/-- Re-normalize policy mass after Lean has rejected invalid tactics.
The tactic generator already softmaxes model log-probabilities over sampled
candidates; after filtering to executable tactics, conditioning on validity is
equivalent to dividing the remaining probability mass by its valid total. -/
private def normalizeCheckedPriors (children : Array CheckedChild) : Array Float :=
  if children.isEmpty then
    #[]
  else
    let weights := children.map fun child =>
      if child.prior > 0.0 then child.prior else 0.0
    let total := weights.foldl (init := (0.0 : Float)) fun acc weight => acc + weight
    if total <= (0.0 : Float) then
      let uniform := 1.0 / children.size.toFloat
      children.map fun _ => uniform
    else
      weights.map fun weight => weight / total

def expand (tg : TacGen) (se : StateEval) (node : NodeType) : TacticM (Array (EdgeData × NodeData)) := do
  if let .ok data := node.data then
    let mut checked := #[]
    let s₀ := data.state
    s₀.restore
    let tactics ← tg (← getUnsolvedGoals)
    for (t, ps, p) in tactics do
      s₀.restore
      if let some s' ← evalTacticStr t (reap.heartbeats.get (← getOptions)) then
        s'.restore
        let goals ← getUnsolvedGoals
        let score ← if goals.isEmpty then pure 0.0 else se goals
        checked := checked.push {
          tacticStr := t
          premise := ps
          prior := p
          state := s'
          score := score
        }

    let priors := normalizeCheckedPriors checked
    return checked.zipIdx.map fun childAndIdx =>
      let child := childAndIdx.1
      let i := childAndIdx.2
      -- No virtual visit: edge starts unvisited so the first PUCT selection
      -- reflects the prior, not a phantom Q value. The child node still
      -- carries `score` so we can back it up on the first real rollout.
      (⟨ child.tacticStr, child.premise, priors[i]!, 0.0, 0, false ⟩,
        .ok ⟨child.state, child.score, 0⟩)
  else
    return #[]

def c_base := 19652.0
def c_init := 2.5
/-- Discount used by AlphaProof-style PUCT when mapping edge values V(s,a) to
positive action values Q(s,a) = gamma^(-V(s,a)-1). -/
def discountFactor := 0.99
/-- Fixed penalty used to initialize an unvisited edge from the parent state's
value estimate: V_init(s,a) = V(s) - fpuPenalty. -/
def fpuPenalty := 32.0
/-- Each tactic consumes one environment step with reward -1, so an edge value
is one step worse than the resulting child state's value. -/
def tacticStepCost := 1.0

private def fmax (a b : Float) : Float := if a ≥ b then a else b

private def qFromSearchValue (v : Float) : Float :=
  if v == (0.0 - Float.inf) then
    0.0 - Float.inf
  else
    let exponent := -v - tacticStepCost
    Float.exp (Float.log discountFactor * exponent)

/-- Whether an edge/child pair is a live candidate we may still pick.
An edge is dead when either (a) the child is an `.error` (the tactic failed),
or (b) we have explicitly marked this tactic/edge as `exhausted`. -/
private def isLive (e : EdgeData) (n : NodeData) : Bool :=
  match n with
  | .error _ => false
  | .ok _ => !e.exhausted

def computeScores (node : NodeType) : Array Float :=
  -- Continue to use the node visit count as N(s). This preserves prior-driven
  -- first-choice behavior immediately after expansion, while edge statistics
  -- store AlphaProof-style V(s,a) values.
  let N := NodeData.visitCount node.data
  -- Adaptive exploration coefficient (AlphaZero style)
  let c := Float.log ((1.0 + N.toFloat + c_base) / c_base) + c_init
  node.children.map fun (e, n) =>
    if !isLive e n then
      -- dead child: never select
      0.0 - Float.inf
    else
      let parentValue := match node.data with
        | .error _ => 0.0 - Float.inf
        | .ok data => data.score
      let v := if e.visitCount == 0 then
        parentValue - fpuPenalty
      else
        e.totalValue / e.visitCount.toFloat
      let q := qFromSearchValue v
      let u := c * e.prior * N.toFloat.sqrt / (1.0 + e.visitCount.toFloat)
      -- AlphaProof-style PUCT: transform V(s,a) into a positive Q(s,a).
      q + u

/-- Pick the child to descend into. Returns `none` if there is none to pick,
either because the node has no children yet or because every child is
dead/exhausted. MCTS treats this as a cue to try expanding the node again. -/
def selectChild (node : NodeType) : Option Nat :=
  if node.children.isEmpty then none
  else
    let scores := computeScores node
    Id.run do
      let mut bestIdx : Option Nat := none
      let mut bestScore := -Float.inf
      for (score, i) in scores.zipIdx do
        -- Exclude strictly -inf candidates explicitly so "all dead" ⇒ none.
        if score > -Float.inf && score > bestScore then
          bestIdx := some i
          bestScore := score
      return bestIdx

def updateEdge (_parent : NodeData) (e : EdgeData) (child : NodeData) : EdgeData :=
  match child with
  | .ok data =>
    let edgeValue := data.score - tacticStepCost
    { e with
      totalValue := e.totalValue + edgeValue
      visitCount := e.visitCount + 1 }
  | .error _ =>
    -- `error` children are dead from birth (score = -∞ in the selector). This
    -- branch is unreachable in practice because MCTS `expand` filters invalid
    -- tactics before creating children; handle it defensively.
    { e with visitCount := e.visitCount + 1, exhausted := true }

private def findIncomingEdge?
    (nodes : Array (Node NodeData (EdgeData × Nat))) (childIdx : Nat) :
    Option (Nat × Nat) := Id.run do
  for nodeAndIdx in nodes.zipIdx do
    let parentIdx := nodeAndIdx.2
    let node := nodeAndIdx.1
    for edgeAndIdx in node.children.zipIdx do
      if edgeAndIdx.1.2 == childIdx then
        return some (parentIdx, edgeAndIdx.2)
  return none

private partial def solutionTacticsCore
    (nodes : Array (Node NodeData (EdgeData × Nat))) (fuel : Nat) (nodeIdx : Nat)
    (acc : List String) : Option (List String) :=
  if nodeIdx == 0 then
    some acc
  else if fuel == 0 then
    none
  else
    match findIncomingEdge? nodes nodeIdx with
    | none => none
    | some (parentIdx, edgeIdx) =>
        match nodes[parentIdx]? with
        | none => none
        | some parent =>
            match parent.children[edgeIdx]? with
            | none => none
            | some (edge, _) =>
                solutionTacticsCore nodes (fuel - 1) parentIdx (edge.tacticStr :: acc)

private def solutionTactics?
    (nodes : Array (Node NodeData (EdgeData × Nat))) (nodeIdx : Nat) : Option (Array String) :=
  (solutionTacticsCore nodes nodes.size nodeIdx []).map List.toArray

private def markNodeError (nodeIdx : Nat) (message : String) :
    StateT (Array (Node NodeData (EdgeData × Nat))) TacticM Unit := do
  modify fun nodes =>
    let nodes :=
      match nodes[nodeIdx]? with
      | none => nodes
      | some node => nodes.set! nodeIdx { node with data := .error message }
    match findIncomingEdge? nodes nodeIdx with
    | none => nodes
    | some (parentIdx, edgeIdx) =>
        match nodes[parentIdx]? with
        | none => nodes
        | some parent =>
            match parent.children[edgeIdx]? with
            | none => nodes
            | some (edge, childIdx) =>
                let edge := { edge with exhausted := true }
                nodes.set! parentIdx
                  { parent with children := parent.children.set! edgeIdx (edge, childIdx) }

private def findSolvedNode?
    (nodes : Array (Node NodeData (EdgeData × Nat))) : TacticM (Option Nat) := do
  for nodeAndIdx in nodes.zipIdx do
    let node := nodeAndIdx.1
    let nodeIdx := nodeAndIdx.2
    match node.data with
    | .error _ => pure ()
    | .ok data =>
        if ← Reap.TreeSearch.isSolved data.state then
          return some nodeIdx
  return none

private def exprContainsConst (declName : Name) (e : Expr) : Bool :=
  e.foldConsts false fun constName found =>
    found || constName == declName || (Lean.privateToUserName? constName).getD constName == declName

private def nameBaseString? : Name → Option String
  | .anonymous => none
  | .str _ s => some s
  | .num _ n => some (toString n)

private def tacticMentionsDeclName (declName : Name) (tacticStr : String) : Bool :=
  let userDeclName := (Lean.privateToUserName? declName).getD declName
  let fullName := userDeclName.toString
  let baseName? := nameBaseString? userDeclName
  tacticStr.contains fullName ||
    match baseName? with
    | some baseName => baseName.length > 3 && tacticStr.contains baseName
    | none => false

private def tacticsMentionCurrentDecl (tactics : Array String) : TacticM Bool := do
  let some declName ← Term.getDeclName? | return false
  return tactics.any (tacticMentionsDeclName declName)

private def rootProofContainsCurrentDecl (rootGoals : List MVarId) : TacticM Bool := do
  let some declName ← Term.getDeclName? | return false
  for goal in rootGoals do
    let some proof ← getExprMVarAssignment? goal | continue
    let proof ← instantiateMVars proof
    if exprContainsConst declName proof then
      return true
  return false

private def anyAssignmentContainsCurrentDecl : TacticM Bool := do
  let some declName ← Term.getDeclName? | return false
  for mvarId in (← getMCtx).getExprAssignmentDomain do
    let some proof ← getExprMVarAssignment? mvarId | continue
    let proof ← instantiateMVars proof
    if exprContainsConst declName proof then
      return true
  return false

inductive FinalReplayResult where
  | valid (state : Tactic.SavedState)
  | invalid (message : String)

private def validateFinalReplay
    (rootState : Tactic.SavedState) (rootGoals : List MVarId) (tactics : Array String)
    (heartbeats : Nat) : TacticM FinalReplayResult := do
  let savedState ← Tactic.saveState
  let savedMessages := (← getThe Core.State).messages
  let result ← try
    if ← tacticsMentionCurrentDecl tactics then
      pure (.invalid "final proof text references the declaration being proved")
    else
      rootState.restore
      modifyThe Core.State fun st => { st with messages := {} }
      let mut failure : Option String := none
      for tacticStr in tactics do
        if failure.isNone then
          if (← evalTacticStr tacticStr heartbeats).isNone then
            failure := some s!"final replay rejected tactic: {tacticStr}"
      if let some msg := failure then
        pure (.invalid msg)
      else
        Term.synthesizeSyntheticMVarsNoPostponing
        pruneSolvedGoals
        if (← getThe Core.State).messages.hasErrors then
          pure (.invalid "final replay produced Lean errors")
        else if !(← getUnsolvedGoals).isEmpty then
          pure (.invalid "final replay left unsolved goals")
        else if ← rootProofContainsCurrentDecl rootGoals then
          pure (.invalid "final proof self-references the root proof")
        else if ← anyAssignmentContainsCurrentDecl then
          pure (.invalid "final proof self-references the declaration being proved")
        else
          pure (.valid (← Tactic.saveState))
  catch _ =>
    pure (.invalid "final replay threw an exception")
  savedState.restore
  modifyThe Core.State fun st => { st with messages := savedMessages }
  return result

private def validateCandidateSolution
    (rootState : Tactic.SavedState) (rootGoals : List MVarId) (nodeIdx : Nat) :
    StateT (Array (Node NodeData (EdgeData × Nat))) TacticM
      (Option (Nat × Tactic.SavedState)) := do
  let nodes ← get
  match solutionTactics? nodes nodeIdx with
  | none =>
      markNodeError nodeIdx "could not reconstruct final replay path"
      return none
  | some tactics =>
      match ← validateFinalReplay rootState rootGoals tactics (reap.heartbeats.get (← getOptions)) with
      | .valid state => return some (nodeIdx, state)
      | .invalid msg =>
          markNodeError nodeIdx msg
          return none

def updateNode (node : NodeType) : NodeData :=
  match node.data with
  | .error msg => .error msg
  | .ok data =>
    let visitCount := data.visitCount + 1
    -- Max backup on V(s,a): node value V(s) = max_a V(s,a). If no live child
    -- edge has been visited, preserve the node's current state-value estimate
    -- so the node can be revisited and expanded again later.
    let bestV := node.children.foldl (init := (0.0 - Float.inf)) fun acc (e, n) =>
      if isLive e n && e.visitCount > 0 then
        fmax acc (e.totalValue / e.visitCount.toFloat)
      else
        acc
    .ok { data with
      score := if bestV == (0.0 - Float.inf) then data.score else bestV,
      visitCount := visitCount
    }

private partial def monteCarloTreeSearchVerified
    (tg : TacGen) (se : StateEval)
    (rootState : Tactic.SavedState) (rootGoals : List MVarId) (rootScore : Float)
    (maxNodes := MCTS.defaultMaxNodes)
    (maxSteps := MCTS.defaultMaxSteps) :
    TacticM (Option (Nat × Tactic.SavedState) × Array (Node NodeData (EdgeData × Nat))) :=
  StateT.run (s := #[ { data := NodeData.ok ⟨rootState, rootScore, 0⟩ } ]) do
    let mut step := 0
    while (← get).size < maxNodes && step < maxSteps do
      let result ← _root_.TreeSearch.mctsStep
        (fun x => x.isTerminal)
        (expand tg se)
        (fun x => return selectChild x)
        (fun p e c => return updateEdge p e c)
        (fun x => return updateNode x)
        0
      let mut candidate? := result
      let mut accepted : Option (Nat × Tactic.SavedState) := none
      let mut keepChecking := true
      while keepChecking && accepted.isNone do
        match candidate? with
        | some k =>
            accepted ← validateCandidateSolution rootState rootGoals k
            candidate? := none
        | none =>
            let nodes ← get
            candidate? ← findSolvedNode? nodes
            if candidate?.isNone then
              keepChecking := false
      if let some result := accepted then
        return some result

      step := step + 1
    return none

structure PPNodeData where
  pp : List String
  value : Float
  visitCount : Nat
deriving ToJson

structure PPEdgeData where
  tacticStr : String
  premise : Array PremiseSelectionResult
  prior : Float
  totalValue : Float
  visitCount : Nat
  exhausted : Bool
  live : Bool
  q : Option Float
  u : Option Float
  qPlusU : Option Float
deriving ToJson, Inhabited

private def computeEdgeBreakdown (parent : NodeData) (e : EdgeData) (child : NodeData) :
    Bool × Option Float × Option Float × Option Float :=
  let live := isLive e child
  if !live then
    (false, none, none, none)
  else
    let N := NodeData.visitCount parent
    let c := Float.log ((1.0 + N.toFloat + c_base) / c_base) + c_init
    let parentValue := match parent with
      | .error _ => 0.0 - Float.inf
      | .ok data => data.score
    let v := if e.visitCount == 0 then
      parentValue - fpuPenalty
    else
      e.totalValue / e.visitCount.toFloat
    let q := qFromSearchValue v
    let u := c * e.prior * N.toFloat.sqrt / (1.0 + e.visitCount.toFloat)
    (true, some q, some u, some (q + u))

private def ppEdgeData (parent : NodeData) (e : EdgeData) (child : NodeData) : PPEdgeData :=
  let (live, q, u, qPlusU) := computeEdgeBreakdown parent e child
  {
    tacticStr := e.tacticStr
    premise := e.premise
    prior := e.prior
    totalValue := e.totalValue
    visitCount := e.visitCount
    exhausted := e.exhausted
    live := live
    q := q
    u := u
    qPlusU := qPlusU
  }

def ppNodeData (node : NodeData) : TacticM PPNodeData := do
  node.restore
  let pp ← (← getUnsolvedGoals).mapM fun g => return toString (← Meta.ppGoal g)
  return ⟨ pp, ← node.priority, NodeData.visitCount node ⟩

def ppNode (nodes : Array (Node NodeData (EdgeData × Nat)))
    (node : Node NodeData (EdgeData × Nat)) : TacticM Json := do
  let children := node.children.map fun (e, childIdx) =>
    match nodes[childIdx]? with
    | some child => (ppEdgeData node.data e child.data, childIdx)
    | none => unreachable!
  let data := ← Reap.TreeSearch.ppNodeData node.data
  return Json.mkObj [
    ("data", toJson data),
    ("children", toJson children)
  ]

end MCTS

open MCTS in
def reapMCTS (tg : TacGen) (se : StateEval)
    (maxNodes := MCTS.defaultMaxNodes)
    (maxSteps := MCTS.defaultMaxSteps) : TacticM Unit := do
  withCumulativeWallClockTime "reap.wall.mcts.total" do
    let rootState ← Tactic.saveState
    let rootGoals ← getUnsolvedGoals
    let rootScore ← if rootGoals.isEmpty then pure 0.0 else se rootGoals
    let (result, nodes) ← monteCarloTreeSearchVerified tg se rootState rootGoals rootScore maxNodes maxSteps
    let k := result.map Prod.fst

    let ppNodes ← nodes.mapM (MCTS.ppNode nodes)
    let info := json%{
      solution : $k,
      nodes : $ppNodes
    }
    communicate info

    if let some (_, state) := result then
      state.restore

  printCumulativeWallClockTimes

end Reap.TreeSearch
