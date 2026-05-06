module
public meta import Lean
public meta import Reap.Options
public meta import Reap.PremiseSelection.API
public meta import Reap.Tactic.WallClock
public meta import TreeSearch.BestFirst
public meta import TreeSearch.MCTS
open Lean Meta Elab Tactic TreeSearch
open Reap.WallClock

public meta section

namespace Reap.TreeSearch

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

namespace MCTS
structure NodeData where
  state : Tactic.SavedState
  valueSum : Float
  numVisit : Nat := 0

namespace NodeData
def value (node : NodeData) : Float :=
  node.valueSum / node.numVisit.toFloat

def isTerminal (node : NodeData) : TacticM Bool :=
  TreeSearch.isSolved node.state

def restore (node : NodeData) : TacticM Unit :=
  node.state.restore

end NodeData

def ppNodeData (node : NodeData) : TacticM Json := do
  node.state.restore
  let pp ← (← getUnsolvedGoals).mapM fun g => do return toString (← Meta.ppGoal g)
  return json%{
    state: $(pp),
    valueSum: $(node.valueSum),
    numVisit: $(node.numVisit)
  }

def ppNode {ε} [ToJson ε] (node : Node NodeData ε) : TacticM Json := do
  return json%{
    data: $(← ppNodeData node.data),
    children: $(node.children)
  }

structure EdgeData where
  tacticStr : String
  premise : Array PremiseSelectionResult
  probability : Float
  value : Float
  numVisit : Nat := 0
deriving ToJson

def visitNode (tg : TacGen) (se : StateEval) (node : NodeData) : TacticM (NodeData × Array (EdgeData × NodeData)) := do
  node.state.restore
  let g ← getUnsolvedGoals
  let p' ← if g.isEmpty then
    pure Float.inf
  else
    se g
  let node' := { node with valueSum := p' }

  let tactics ← tg g
  let mut children := #[]
  for (t, ps, prior) in tactics do
    node.state.restore
    if let some s' ← evalTacticStr t (reap.heartbeats.get (← getOptions)) then
      -- TODO: merge nodes
      s'.restore
      children := children.push (⟨ t, ps, prior.exp, 0, 0 ⟩, ⟨ s', 0.0, node.numVisit ⟩)

  return (node', children)


abbrev NodeType := Node NodeData (EdgeData × NodeData)

def scaledNatToFloat (n : Nat) : Float :=
  n.toFloat / 1000.0

def computePUCTScores (node : NodeType) : TacticM (Array Float) := do
  let opts ← getOptions
  let cBase := reap.c_base.get opts |>.toFloat
  let cInit := scaledNatToFloat (reap.c_init.get opts)
  let visitDiscount := scaledNatToFloat (reap.visit_discount.get opts)
  let priorTemperature := reap.prior_temperature.get opts |>.toFloat

  -- exploration factor
  let N := node.data.numVisit.toFloat
  let c := cInit + Float.log ((N + cBase + 1) / cBase)
  return node.children.map fun (e, n) =>
    let Q := Float.pow visitDiscount (n.value - 1)
    let U := c * Float.pow e.probability (1 / priorTemperature) * N.sqrt / (e.numVisit.toFloat + 1)
    Q + U

def selectChild (node : NodeType) : TacticM (Option Nat) := do
  let scores ← computePUCTScores node
  -- I could not find a convenient way in Std to compute argmax of an array
  return Id.run do
    let mut bestIdx := none
    let mut bestScore := -Float.inf
    for (score, i) in scores.zipIdx do
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
      numVisit := node.data.numVisit + 1
      valueSum := node.data.valueSum + leaf.valueSum
  }

structure PPNodeData where
  pp : List String
  value : Float
deriving ToJson

end MCTS

open MCTS in
def reapMCTS (tg : TacGen) (se : StateEval)
    (maxNodes := MCTS.defaultMaxNodes)
    (maxSteps := MCTS.defaultMaxSteps) : TacticM Unit := unsafe do
  withCumulativeWallClockTime "reap.wall.mcts.total" do
    let (k, nodes) ← monteCarloTreeSearch (ε := EdgeData)
      (fun x => x.isTerminal)
      (fun x => visitNode tg se x.data)
      (fun x => selectChild x)
      (fun _ e _ l => return updateEdge e l)
      (fun x l => return updateNode x l)
      ⟨ (← Tactic.saveState), 0.0, 0 ⟩
      maxNodes maxSteps

    let ppNodes ← nodes.mapM ppNode
    let info := json%{
      solution : $k,
      nodes : $ppNodes
    }
    communicate info

    if let some k := k then
      let some {data := node, ..} := nodes[k]? | unreachable!
      node.state.restore

  printCumulativeWallClockTimes

end Reap.TreeSearch
