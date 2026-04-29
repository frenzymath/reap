module
public meta import Lean
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

def withHeartbeats {m : Type _ → Type _} {α : Type _} [Monad m] [MonadWithReaderOf Core.Context m] (heartbeats : Nat) : m α → m α :=
  withReader (fun s => { s with maxHeartbeats := heartbeats })

def evalTacticStr (str : String) (heartbeats : Nat) : TacticM (Option Tactic.SavedState) := do
  withCumulativeWallClockTime "reap.wall.tactic_eval" do
    let .ok stx := Parser.runParserCategory (← getEnv) `tactic str | return none
    try
      let success ← tryCatchRuntimeEx (handler := fun _ => return false) do
        withHeartbeats heartbeats <| evalTactic stx
        return true
      if success then
        pruneSolvedGoals
        if (← getThe Core.State).messages.hasErrors then
          return none
      else
        return none
    catch _ => return none
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
        return (t, .ok { state := s', score := p', visitCount := 0 })
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
      (expand tg se) (.ok { state := (← Tactic.saveState), score := 0.0, visitCount := 0 }) maxNodes
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
  totalValue : Float := 0.0
  visitCount : Nat := 0
  exhausted : Bool := false
deriving ToJson

abbrev NodeType := Node NodeData (EdgeData × NodeData)

structure CheckedChild where
  tacticStr : String
  premise : Array PremiseSelectionResult
  prior : Float
  state : Tactic.SavedState
  score : Float

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
      (⟨ child.tacticStr, child.premise, priors[i]!, 0.0, 0, false ⟩,
        .ok { state := child.state, score := child.score, visitCount := 0 })
  else
    return #[]

def c_base := 19652.0
def c_init := 2.5
def discountFactor := 0.99
def fpuPenalty := 32.0
def tacticStepCost := 1.0

private def fmax (a b : Float) : Float := if a >= b then a else b

private def qFromSearchValue (v : Float) : Float :=
  let exponent := -v - tacticStepCost
  Float.exp (Float.log discountFactor * exponent)

private def isLive (e : EdgeData) (n : NodeData) : Bool :=
  match n with
  | .error _ => false
  | .ok _ => !e.exhausted

def computeScores (node : NodeType) : Array Float :=
  let N := NodeData.visitCount node.data
  let c := Float.log ((1.0 + N.toFloat + c_base) / c_base) + c_init
  let parentValue := match node.data with
    | .error _ => -Float.inf
    | .ok data => data.score
  node.children.map fun (e, n) =>
    if !isLive e n then
      -Float.inf
    else
      let v := if e.visitCount == 0 then
        parentValue - fpuPenalty
      else
        e.totalValue / e.visitCount.toFloat
      let q := qFromSearchValue v
      let u := c * e.prior * N.toFloat.sqrt / (1.0 + e.visitCount.toFloat)
      q + u

def selectChild (node : NodeType) : Option Nat :=
  let scores := computeScores node
  -- I could not find a convenient way in Std to compute argmax of an array
  Id.run do
    let mut bestIdx := none
    let mut bestScore := -Float.inf
    for (score, i) in scores.zipIdx do
      if score > bestScore then
        bestIdx := some i
        bestScore := score
    return bestIdx

def updateEdge (_parent : NodeData) (e : EdgeData) (child : NodeData) : EdgeData :=
  match child with
  | .ok data =>
      if data.score == -Float.inf then
        { e with visitCount := e.visitCount + 1, exhausted := true }
      else
        let edgeValue := data.score - tacticStepCost
        { e with
          totalValue := e.totalValue + edgeValue
          visitCount := e.visitCount + 1 }
  | .error _ =>
      { e with visitCount := e.visitCount + 1, exhausted := true }

private def isExhausted (node : NodeType) : Bool :=
  node.expanded && node.children.all (fun (e, n) => !isLive e n)

def updateNode (node : NodeType) : NodeData :=
  match node.data with
  | .error msg => .error msg
  | .ok data =>
      let visitCount := data.visitCount + 1
      if isExhausted node then
        .ok { data with score := -Float.inf, visitCount := visitCount }
      else
        let bestV := node.children.foldl (init := -Float.inf) fun acc (e, n) =>
          if isLive e n && e.visitCount > 0 then
            fmax acc (e.totalValue / e.visitCount.toFloat)
          else
            acc
        .ok { data with
          score := if bestV == -Float.inf then data.score else bestV
          visitCount := visitCount }

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

private def exprContainsConst (declName : Name) (e : Expr) : Bool :=
  e.foldConsts false fun constName found =>
    found || constName == declName || (Lean.privateToUserName? constName).getD constName == declName

private def rootProofContainsCurrentDecl (rootGoals : List MVarId) : TacticM Bool := do
  let some declName ← Term.getDeclName? | return false
  for goal in rootGoals do
    let some proof ← getExprMVarAssignment? goal | return false
    let proof ← instantiateMVars proof
    if exprContainsConst declName proof then
      return true
  return false

inductive FinalReplayResult where
  | valid (state : Tactic.SavedState)
  | invalid (message : String)

private def validateFinalReplay
    (rootState : Tactic.SavedState) (rootGoals : List MVarId)
    (tactics : Array String) (heartbeats : Nat) : TacticM FinalReplayResult := do
  let savedState ← Tactic.saveState
  let result ← try
    rootState.restore
    let mut failure : Option String := none
    for tacticStr in tactics do
      if failure.isNone then
        match ← evalTacticStr tacticStr heartbeats with
        | none => failure := some s!"final replay rejected tactic: {tacticStr}"
        | some state => state.restore
    if let some msg := failure then
      pure (.invalid msg)
    else if (← getThe Core.State).messages.hasErrors then
      pure (.invalid "final replay produced Lean errors")
    else if !(← getUnsolvedGoals).isEmpty then
      pure (.invalid "final replay left unsolved goals")
    else if ← rootProofContainsCurrentDecl rootGoals then
      pure (.invalid "final proof self-references the declaration being proved")
    else
      pure (.valid (← Tactic.saveState))
  catch _ =>
    pure (.invalid "final replay threw an exception")
  savedState.restore
  return result

private partial def monteCarloTreeSearchVerified
    (tg : TacGen) (se : StateEval)
    (rootState : Tactic.SavedState) (rootGoals : List MVarId) (rootScore : Float)
    (maxNodes := MCTS.defaultMaxNodes)
    (maxSteps := MCTS.defaultMaxSteps) :
    TacticM (Option (Nat × Tactic.SavedState) × Array (Node NodeData (EdgeData × Nat))) :=
  StateT.run (s := #[ { data := NodeData.ok { state := rootState, score := rootScore, visitCount := 0 } } ]) do
    let mut step := 0
    while (← get).size < maxNodes && step < maxSteps do
      let result ← _root_.TreeSearch.mctsStep
        (fun x => x.isTerminal)
        (expand tg se)
        (fun x => return selectChild x)
        (fun p e c => return updateEdge p e c)
        (fun x => return updateNode x)
        0
      if let some k := result then
        let nodes ← get
        match solutionTactics? nodes k with
        | none =>
            markNodeError k "could not reconstruct final replay path"
        | some tactics =>
            match ← validateFinalReplay rootState rootGoals tactics (reap.heartbeats.get (← getOptions)) with
            | .valid state => return some (k, state)
            | .invalid msg => markNodeError k msg
      step := step + 1
    return none

structure PPNodeData where
  pp : List String
  value : Float
  visitCount : Nat
deriving ToJson

def ppNodeData (node : NodeData) : TacticM PPNodeData := do
  node.restore
  let pp ← (← getUnsolvedGoals).mapM fun g => return toString (← Meta.ppGoal g)
  return ⟨ pp, ← node.priority, NodeData.visitCount node ⟩

def ppNode (_nodes : Array (Node NodeData (EdgeData × Nat)))
    (node : Node NodeData (EdgeData × Nat)) : TacticM Json := do
  return json%{
    data: $(← Reap.TreeSearch.ppNodeData node.data),
    children: $(node.children)
  }

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
