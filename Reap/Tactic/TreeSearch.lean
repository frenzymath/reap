module
public meta import Lean
public meta import Reap.Options
public meta import Reap.PremiseSelection.API
public meta import Reap.Tactic.State
public meta import Reap.Tactic.Step
public meta import Reap.Tactic.WallClock
public meta import TreeSearch.BestFirst
public meta import TreeSearch.MCTS
open Lean Meta Elab Tactic TreeSearch
open Reap.WallClock

public meta section

namespace Reap.TreeSearch

def writeRawTree (path : String) (obj : Json) : IO Unit := do
  if !path.isEmpty then
    IO.FS.withFile path .write fun h =>
      h.putStrLn obj.compress

def getGoalTypes : TacticM (Option (Array Expr)) := do
  let goals ← getUnsolvedGoals
  let mut goalTypes := #[]
  for g in goals do
    let t ← g.getTypeCleanup
    if t.hasExprMVar then
      return none
    else
      goalTypes := goalTypes.push t
  return some goalTypes

def collectGoalMVars (goal : MVarId) : TacticM (Array MVarId) := goal.withContext do
  let collect : StateRefT CollectMVars.State MetaM Unit := do
    Meta.collectMVars (← goal.getType)
    for localDecl in (← getLCtx) do
      unless localDecl.isImplementationDetail do
        Meta.collectMVars localDecl.type
        if let some value := localDecl.value? then
          Meta.collectMVars value
  let (_, state) ← collect.run {}
  return state.result

def sharesMVar (a b : Array MVarId) : Bool :=
  a.any fun x => b.contains x

def replaceLabel (labels : Array Nat) (oldLabel newLabel : Nat) : Array Nat :=
  labels.map fun label => if label == oldLabel then newLabel else label

def dependencyLabels (deps : Array (Array MVarId)) : Array Nat :=
  Id.run do
    let mut labels := (List.range deps.size).toArray
    for i in List.range deps.size do
      for j in List.range deps.size do
        if i < j && sharesMVar deps[i]! deps[j]! then
          let li := labels[i]!
          let lj := labels[j]!
          let keep := min li lj
          let drop := max li lj
          labels := replaceLabel labels drop keep
    return labels

structure GoalGroup where
  label : Nat
  indices : Array Nat
  goals : Array MVarId
deriving Inhabited

def addGoalToGroup (groups : Array GoalGroup) (label index : Nat) (goal : MVarId) :
    Array GoalGroup :=
  Id.run do
    let mut groups' := groups
    let mut found := false
    for i in List.range groups.size do
      let group := groups[i]!
      if group.label == label then
        groups' := groups'.set! i {
          group with
            indices := group.indices.push index
            goals := group.goals.push goal
        }
        found := true
    if found then
      return groups'
    else
      return groups'.push { label, indices := #[index], goals := #[goal] }

def goalDependencyGroups : TacticM (Array GoalGroup) := do
  let goals := (← getUnsolvedGoals).toArray
  let deps ← goals.mapM collectGoalMVars
  let labels := dependencyLabels deps
  let mut groups := #[]
  for i in List.range goals.size do
    groups := addGoalToGroup groups labels[i]! i goals[i]!
  return groups

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

abbrev TacGen := List MVarId → MetaM (Array (String × Array PremiseSelectionResult × Float))
abbrev StateEval := List MVarId → MetaM Float

structure SearchHyperparameters where
  cBase : Float
  cInit : Float
  visitDiscount : Float
  priorTemperature : Float
  progressiveSamplingC : Float
  progressiveSamplingAlpha : Float

def scaledNatToFloat (n : Nat) : Float :=
  n.toFloat / 1000.0

namespace SearchHyperparameters

def fromOptions (opts : Options) : SearchHyperparameters := {
  cBase := reap.c_base.get opts |>.toFloat
  cInit := scaledNatToFloat <| reap.c_init.get opts
  visitDiscount := scaledNatToFloat <| reap.visit_discount.get opts
  priorTemperature := reap.prior_temperature.get opts |>.toFloat
  progressiveSamplingC := scaledNatToFloat <| reap.progressive_sampling_c.get opts
  progressiveSamplingAlpha := scaledNatToFloat <| reap.progressive_sampling_alpha.get opts
}

end SearchHyperparameters

namespace MCTS
inductive NodeKind where
  | orNode
  | andNode
deriving BEq, Inhabited

instance : ToJson NodeKind where
  toJson
  | .orNode => "OR"
  | .andNode => "AND"

structure NodeData where
  state : Tactic.SavedState
  key : StateKey
  toPlay : NodeKind
  isPartial : Bool
  isSolved : Bool
  valueSum : Float
  numVisit : Nat
  numEvaluations : Nat

namespace NodeData
def fromState (toPlay := NodeKind.orNode) (isPartial := false) : TacticM NodeData := do
  pure {
    state := ← Tactic.saveState
    key := ← stateKey
    toPlay
    isPartial
    isSolved := (← getUnsolvedGoals).isEmpty
    valueSum := 0.0
    numVisit := 0
    numEvaluations := 0
  }

def value (node : NodeData) : Float :=
  if node.numVisit == 0 then 0.0 else node.valueSum / node.numVisit.toFloat

def restore (node : NodeData) : TacticM Unit :=
  node.state.restore

def isTerminal (node : NodeData) : TacticM Bool := do
  node.restore
  return (← getUnsolvedGoals).isEmpty

end NodeData

structure EdgeData where
  tacticStr : String
  premise : Array PremiseSelectionResult
  probability : Float
  value : Float
  numVisit : Nat := 0
  isFocus : Bool := false
  focusIndices : Array Nat := #[]
deriving Inhabited, ToJson

abbrev NodeType := Node NodeData (EdgeData × NodeData)

abbrev SearchM := IndexedTreeT NodeData EdgeData TacticM

def getNode! (nodeIdx : Nat) : SearchM (Node NodeData (EdgeData × Nat)) := do
  let nodes ← get
  let some node := nodes[nodeIdx]? | throwError "MCTS node index out of bounds: {nodeIdx}"
  return node

partial def replaySolvedNode (ctx : ProofCheckContext) (heartbeats : Nat)
    (nodes : Array (Node NodeData (EdgeData × Nat))) (nodeIdx : Nat) : TacticM Unit := do
  let some node := nodes[nodeIdx]? | unreachable!
  match node.data.toPlay with
  | .orNode =>
      if (← getUnsolvedGoals).isEmpty then
        return ()
      let solvedChild := node.children.find? fun (edge, childIdx) =>
        Id.run do
          let some child := nodes[childIdx]? | unreachable!
          return (!edge.isFocus) && child.data.isSolved
      let some (edge, childIdx) := solvedChild | unreachable!
      match ← evalTacticStrNoFinalCheck ctx edge.tacticStr heartbeats with
      | .ok _ => replaySolvedNode ctx heartbeats nodes childIdx
      | .error err => throwError "MCTS proof replay failed on tactic {edge.tacticStr}: {(toJson err).compress}"
  | .andNode =>
      let goals := (← getUnsolvedGoals).toArray
      for (edge, childIdx) in node.children do
        if edge.isFocus then
          let groupGoals := edge.focusIndices.map fun focusIndex =>
            Id.run do
              let some goal := goals[focusIndex]? | unreachable!
              return goal
          setGoals groupGoals.toList
          replaySolvedNode ctx heartbeats nodes childIdx
      setGoals goals.toList
      pruneSolvedGoals

def nodeStructurallySolved (node : NodeType) : Bool :=
  match node.data.toPlay with
  | .orNode => node.data.isSolved || node.children.any fun (_, child) => child.isSolved
  | .andNode => node.data.isSolved || (!node.children.isEmpty && node.children.all fun (_, child) => child.isSolved)

def refreshNodeSolved (nodeIdx : Nat) : SearchM Unit := do
  let nodeRef ← getNode! nodeIdx
  let node ← resolve nodeRef
  let isSolved := nodeStructurallySolved node
  setAtT nodeIdx { nodeRef with data := { nodeRef.data with isSolved := isSolved } }

def focusProbability (numGoals : Nat) : Float :=
  if numGoals == 0 then 0.0 else 1.0 / numGoals.toFloat

def focusTacticStr (indices : Array Nat) : String :=
  "focus_goals [" ++ String.intercalate ", " (indices.toList.map toString) ++ "]"

def pushFocusChildren (nodeIdx : Nat) (node : NodeData) : SearchM Unit := do
  node.state.restore
  let groups ← goalDependencyGroups
  let probability := focusProbability groups.size
  for group in groups do
    node.state.restore
    setGoals group.goals.toList
    let childData ← NodeData.fromState (isPartial := true)
    discard <| pushChildT nodeIdx {
      tacticStr := focusTacticStr group.indices
      premise := #[]
      probability
      value := 0.0
      isFocus := true
      focusIndices := group.indices
    } childData
  node.state.restore

def childKindAfterTactic : TacticM NodeKind := do
  let groups ← goalDependencyGroups
  return if groups.size > 1 then .andNode else .orNode

def updateDuplicateChild (nodeIdx childPos : Nat) (childData : NodeData) : SearchM Unit := do
  let nodeRef ← getNode! nodeIdx
  let some (_, childIdx) := nodeRef.children[childPos]? | unreachable!
  let childRef ← getNode! childIdx
  setAtT childIdx { childRef with data := { childRef.data with isSolved := childRef.data.isSolved || childData.isSolved } }
  refreshNodeSolved childIdx

def visitNode (ctx : ProofCheckContext) (tg : TacGen) (se : StateEval)
    (nodeIdx : Nat) (node : NodeType) : SearchM Float := do
  if node.data.toPlay == .andNode then
    if node.children.isEmpty then
      pushFocusChildren nodeIdx node.data
      refreshNodeSolved nodeIdx
    return node.data.value

  node.data.state.restore
  let g ← getUnsolvedGoals
  let p' ← if g.isEmpty then
    pure Float.inf
  else
    se g
  let data' := {
    node.data with
      valueSum := node.data.valueSum + p'
      numVisit := node.data.numVisit + 1
      numEvaluations := node.data.numEvaluations + 1
  }
  modifyAtT nodeIdx fun node => { node with data := data' }

  let tactics ← tg g
  let opts ← getOptions
  let heartbeats := reap.heartbeats.get opts
  let priorTemperature := reap.prior_temperature.get opts |>.toFloat
  for (t, ps, prior) in tactics do
    node.data.state.restore
    let result ← if node.data.isPartial then
      evalTacticStrNoFinalCheck ctx t heartbeats
    else
      evalTacticStr ctx t heartbeats
    if result.isOk then
      let probability := (prior / priorTemperature).exp
      let childKind ← childKindAfterTactic
      let childData ← NodeData.fromState childKind node.data.isPartial
      if let some ((e, _), childPos) := node.children.zipIdx.find? fun ((e, c), _) => e.tacticStr == t || c.key == childData.key then
        let e' := { e with probability := e.probability + probability }
        updateDuplicateChild nodeIdx childPos childData
        modifyAtT nodeIdx fun node => {
          node with
            children := node.children.modify childPos fun (_, c) => (e', c)
        }
      else
        let childIdx ← pushChildT nodeIdx {
          tacticStr := t
          premise := ps
          probability
          value := 0.0
        } childData
        if childData.toPlay == .andNode then
          pushFocusChildren childIdx childData
          refreshNodeSolved childIdx
  refreshNodeSolved nodeIdx
  return p'

structure CQU where
  c : Float
  Q : Float
  U : Float
deriving Inhabited, ToJson

def computePUCTScores (params : SearchHyperparameters)
    (node : NodeType) : Array (Float × CQU) :=
  -- exploration factor
  let N := node.data.numVisit.toFloat
  let c := params.cInit + Float.log ((N + params.cBase + 1) / params.cBase)
  let totalMass := (node.children.map fun (e, _) => e.probability).sum
  node.children.map fun (e, n) =>
    let valueScore := params.visitDiscount.pow (n.value - 1)
    let Q := match node.data.toPlay with
      | .orNode => valueScore
      | .andNode => if n.isSolved then -Float.inf else 1 - valueScore
    let p := e.probability / totalMass
    let U := c * p * N.sqrt / (e.numVisit.toFloat + 1)
    let score := Q + U
    (score, { c := c, Q := Q, U := U })

def shouldProgressiveSample (params : SearchHyperparameters) (node : NodeData) : Bool :=
  node.toPlay == .orNode && node.numEvaluations.toFloat <=
    params.progressiveSamplingC * Float.pow node.numVisit.toFloat params.progressiveSamplingAlpha

def ppNodeData (node : NodeData) : TacticM Json := do
  node.state.restore
  let pp ← (← getUnsolvedGoals).mapM fun g => do return toString (← Meta.ppGoal g)
  return json%{
    state: $(pp),
    toPlay: $(node.toPlay),
    isPartial: $(node.isPartial),
    isSolved: $(node.isSolved),
    valueSum: $(node.valueSum),
    numVisit: $(node.numVisit),
    numEvaluations: $(node.numEvaluations)
  }

def ppNode (params : SearchHyperparameters) (arr : Array (Node NodeData (EdgeData × Nat)))
    (node : Node NodeData (EdgeData × Nat)) : TacticM Json := do
  let children ← node.children.mapM fun (e, i) => do
    let some child := arr[i]? | unreachable!
    return (e, child.data)
  let scores := computePUCTScores params { data := node.data, children := children }
  let ppChildren := node.children.zip scores |>.map fun ((e, i), (score, cqu)) => json%{
    edge: $e,
    extra: {
      score: $score,
      c: $cqu.c,
      Q: $cqu.Q,
      U: $cqu.U
    },
    childIndex: $i
  }
  return json%{
    data: $(← ppNodeData node.data),
    children: $ppChildren
  }

def selectChild (params : SearchHyperparameters) (node : NodeType) : Option Nat := do
  if node.children.isEmpty || shouldProgressiveSample params node.data then
    none
  else
    let scores := computePUCTScores params node
    -- I could not find a convenient way in Std to compute argmax of an array
    Id.run do
      let mut bestIdx := none
      let mut bestScore := -Float.inf
      for ((score, _), i) in scores.zipIdx do
        if score > bestScore then
          bestIdx := some i
          bestScore := score
      return bestIdx

def updateEdge (e : EdgeData) (value : Float) : EdgeData :=
  {
    e with
      numVisit := e.numVisit + 1
      value := e.value + value
  }

def backpropValueTowardsMin (node : NodeType) : Float :=
  Id.run do
    let mut value := 1.0
    for (_, child) in node.children do
      if !child.isSolved && child.numVisit > 0 then
        value := min value child.value
    return value

def backupValueForParent (node : NodeType) (value : Float) : Float :=
  match node.data.toPlay with
  | .orNode => value
  | .andNode => backpropValueTowardsMin node

def updateNode (node : NodeType) (value : Float) : NodeData :=
  {
    node.data with
      numVisit := node.data.numVisit + 1
      valueSum := node.data.valueSum + value
  }

partial def reapMCTSStep (ctx : ProofCheckContext) (tg : TacGen) (se : StateEval)
    (params : SearchHyperparameters) (nodeIdx : Nat) : SearchM Float := do
  let x ← getNode! nodeIdx
  let node ← resolve x
  match selectChild params node with
  | none =>
      visitNode ctx tg se nodeIdx node
  | some childPos =>
      let some (_, childIdx) := x.children[childPos]? | unreachable!
      let value ← reapMCTSStep ctx tg se params childIdx
      let x ← getNode! nodeIdx
      let some (edge, _) := x.children[childPos]? | unreachable!
      let edge' := updateEdge edge value
      setAtT nodeIdx { x with children := x.children.modify childPos fun _ => (edge', childIdx) }
      let nodeRef ← getNode! nodeIdx
      let node ← resolve nodeRef
      let data' := updateNode node value
      let x ← getNode! nodeIdx
      setAtT nodeIdx { x with data := data' }
      refreshNodeSolved nodeIdx
      let nodeRef ← getNode! nodeIdx
      let node ← resolve nodeRef
      return backupValueForParent node value

def monteCarloTreeSearch (ctx : ProofCheckContext) (tg : TacGen) (se : StateEval)
    (params : SearchHyperparameters) (start : NodeData)
    (maxNodes := MCTS.defaultMaxNodes) (maxSteps := MCTS.defaultMaxSteps) :
    TacticM (Option Nat × Array (Node NodeData (EdgeData × Nat))) :=
  StateT.run (s := #[ { data := start } ]) do
    let mut step := 0
    while (← get).size <= maxNodes && step < maxSteps do
      discard <| reapMCTSStep ctx tg se params 0
      let root ← getNode! 0
      if root.data.isSolved then
        return some 0
      step := step + 1
    return none

end MCTS

open MCTS in
def reapMCTS (tg : TacGen) (se : StateEval)
    (maxNodes := MCTS.defaultMaxNodes)
    (maxSteps := MCTS.defaultMaxSteps) : TacticM Unit := unsafe do
  let opts ← getOptions
  let path := reap.wall_clock_log_path.get opts
  if !path.isEmpty then
    openLogFile <| .mk path
  let ctx ← mkProofCheckContext
  let params := SearchHyperparameters.fromOptions opts
  let (k, nodes) ← monteCarloTreeSearch ctx tg se params (← NodeData.fromState) maxNodes maxSteps

  let ppNodes ← nodes.mapM (ppNode params nodes)
  let info := json%{
    solution : $k,
    nodes : $ppNodes
  }
  writeRawTree (reap.raw_tree_path.get opts) info

  if k.isSome then
    let heartbeats := reap.heartbeats.get opts
    let some root := nodes[0]? | unreachable!
    let saved ← Tactic.saveState
    try
      root.data.state.restore
      replaySolvedNode ctx heartbeats nodes 0
      match ← checkProof ctx with
      | .ok _ => return ()
      | .error err => throwError "MCTS final proof check failed after replay: {(toJson err).compress}"
    catch ex =>
      saved.restore
      throw ex

end Reap.TreeSearch
