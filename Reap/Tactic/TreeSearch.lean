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

def communicate (obj : Json) : IO Unit :=
  -- HACK: communicate the search tree to parent process in an unnecessarily complicated way
  -- since Lean devs think they are so smart, and we (other devs) don't know what we want
  try
    IO.FS.withFile "/dev/fd/3" .write fun h =>
      h.putStrLn obj.compress
  catch _ => return ()

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
structure NodeData where
  state : Tactic.SavedState
  key : StateKey
  isSolved : Bool
  valueSum : Float
  numVisit : Nat
  numEvaluations : Nat

namespace NodeData
def fromState : TacticM NodeData := do
  pure {
    state := ← Tactic.saveState
    key := ← stateKey
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
deriving ToJson

abbrev NodeType := Node NodeData (EdgeData × NodeData)

abbrev SearchM := IndexedTreeT NodeData EdgeData TacticM

def visitNode (ctx : ProofCheckContext) (tg : TacGen) (se : StateEval)
    (nodeIdx : Nat) (node : NodeType) : SearchM Unit := do
  node.data.state.restore
  let g ← getUnsolvedGoals
  let p' ← if g.isEmpty then
    pure Float.inf
  else
    se g
  let data' := { node.data with valueSum := p', numEvaluations := node.data.numEvaluations + 1 }
  modifyAtT nodeIdx fun node => { node with data := data' }

  let tactics ← tg g
  let opts ← getOptions
  let heartbeats := reap.heartbeats.get opts
  let priorTemperature := reap.prior_temperature.get opts |>.toFloat
  for (t, ps, prior) in tactics do
    node.data.state.restore
    if (← evalTacticStr ctx t heartbeats).isOk then
      let probability := (prior / priorTemperature).exp
      let childData ← NodeData.fromState
      if let some ((e, c), childPos) := node.children.zipIdx.find? fun ((e, c), _) => e.tacticStr == t || c.key == childData.key then
        let e' := { e with probability := e.probability + probability }
        modifyAtT nodeIdx fun node => {
          node with
            data := { node.data with isSolved := node.data.isSolved || c.isSolved || childData.isSolved }
            children := node.children.modify childPos fun (_, c) => (e', c)
        }
      else
        discard <| pushChildT nodeIdx ⟨ t, ps, probability, 0, 0 ⟩ childData

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
    let Q := params.visitDiscount.pow (n.value - 1)
    let p := e.probability / totalMass
    let U := c * p * N.sqrt / (e.numVisit.toFloat + 1)
    let score := Q + U
    (score, { c := c, Q := Q, U := U })

def shouldProgressiveSample (params : SearchHyperparameters) (node : NodeData) : Bool :=
  node.numEvaluations.toFloat <=
    params.progressiveSamplingC * Float.pow node.numVisit.toFloat params.progressiveSamplingAlpha

def ppNodeData (node : NodeData) : TacticM Json := do
  node.state.restore
  let pp ← (← getUnsolvedGoals).mapM fun g => do return toString (← Meta.ppGoal g)
  return json%{
    state: $(pp),
    isSolved: $(node.isSolved),
    valueSum: $(node.valueSum),
    numVisit: $(node.numVisit),
    numEvaluations: $(node.numEvaluations)
  }

def ppNode (params : SearchHyperparameters) (arr : Array (Node NodeData (EdgeData × Nat)))
    (node : Node NodeData (EdgeData × Nat)) : TacticM Json := do
  let children ← node.children.mapM fun (e, i) => do
    let some x := arr[i]? | unreachable!
    return (e, x.data)
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

def updateEdge (e : EdgeData) (leaf : NodeData) : EdgeData :=
  {
    e with
      numVisit := e.numVisit + 1
      value := e.value + leaf.valueSum
  }

def updateNode (node : NodeType) (leaf : NodeData) : NodeData :=
  {
    node.data with
      isSolved := node.data.isSolved || node.children.any fun (_, child) => child.isSolved
      numVisit := node.data.numVisit + 1
      valueSum := node.data.valueSum + leaf.valueSum
  }

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
  let (k, nodes) ← monteCarloTreeSearch (ε := EdgeData)
    (fun x => do x.isTerminal)
    (visitNode ctx tg se)
    (fun x => return selectChild params x)
    (fun _ e _ l => return updateEdge e l)
    (fun x l => return updateNode x l)
    (← NodeData.fromState)
    maxNodes maxSteps

  let ppNodes ← nodes.mapM (ppNode params nodes)
  let info := json%{
    solution : $k,
    nodes : $ppNodes
  }
  communicate info

  if let some k := k then
    let some { data := node, .. } := nodes[k]? | unreachable!
    node.state.restore

end Reap.TreeSearch
