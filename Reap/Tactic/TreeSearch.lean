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

structure NodeState where
  state : Tactic.SavedState
  value : Float
  numVisit : Nat

abbrev NodeData := Except String NodeState

namespace NodeData
def priority : NodeData → TacticM Float
  | .error _ => return Float.inf
  | .ok node => do
      if ← isSolved node.state then
        return Float.inf
      else
        return node.value

def isTerminal : NodeData → TacticM Bool
  | .error _ => pure false
  | .ok node => TreeSearch.isSolved node.state

def restore : NodeData → TacticM Unit
  | .error _ => pure ()
  | .ok node => node.state.restore

end NodeData

def ppNodeData : NodeData → TacticM Json
  | .error message => pure <| json%{ message: $message }
  | .ok node => do
    node.state.restore
    let pp ← (← getUnsolvedGoals).mapM fun g => do return toString (← Meta.ppGoal g)
    return json%{
      state: $(pp),
      value: $(node.value),
      numVisit: $(node.numVisit)
    }

def ppNode {ε} [ToJson ε] (node : Node NodeData ε) : TacticM Json := do
  return json%{
    data: $(← ppNodeData node.data),
    children: $(node.children)
  }

namespace BFS
def expand (tg : TacGen) (se : Option StateEval) : NodeData → TacticM (Array (String × NodeData))
  | .error _ => pure #[]
  | .ok node => do
    node.state.restore
    let tactics ← tg (← getUnsolvedGoals)
    tactics.mapM fun (t, _, Δp) => do
      node.state.restore
      if let some s' ← evalTacticStr t (reap.heartbeats.get (← getOptions)) then
        -- TODO: merge nodes
        s'.restore
        let g ← getUnsolvedGoals
        let p' ← if g.isEmpty then
          pure Float.inf
        else if let some se := se then
          se g
        else
          pure (node.value + Δp)
        return (t, .ok ⟨ s', p', node.numVisit ⟩)
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
      (expand tg se) (.ok ⟨ (← Tactic.saveState), 0.0, 0 ⟩) maxNodes
    let ppNodes ← nodes.mapM ppNode
    let info := json%{
      solution : $k,
      nodes : $ppNodes
    }
    communicate info

    if let some k := k then
      let some {data := .ok node, ..} := nodes[k]? | unreachable!
      node.state.restore
  printCumulativeWallClockTimes

end BFS

namespace MCTS

structure EdgeData where
  tacticStr : String
  premise : Array PremiseSelectionResult
  prior : Float
  visit : Nat := 0
deriving ToJson

abbrev NodeType := Node NodeData (EdgeData × NodeData)

def expand (tg : TacGen) (se : StateEval) (node : NodeType) : TacticM (Array (EdgeData × NodeData)) := do
  if let .ok nodeState := node.data then
    let mut ret := #[]
    nodeState.state.restore
    let tactics ← tg (← getUnsolvedGoals)
    for (t, ps, p) in tactics do
      nodeState.state.restore
      if let some s' ← evalTacticStr t (reap.heartbeats.get (← getOptions)) then
        s'.restore
        -- TODO: figure out initialization of nodes
        let score ← se (← getUnsolvedGoals)
        ret := ret.push (⟨ t, ps, p, 1 ⟩, .ok ⟨ s', score, 1 ⟩)
      else
        ret := ret.push (⟨ t, #[], 0, 0 ⟩, .error "")

    return ret
  else
    return #[]

def scaledNatToFloat (n : Nat) : Float :=
  n.toFloat / 100.0

def computeScores (node : NodeType) : TacticM (Array Float) := do
  let opts ← getOptions
  let cBase := scaledNatToFloat (reap.c_base.get opts)
  let cInit := scaledNatToFloat (reap.c_init.get opts)
  let visitDiscount := scaledNatToFloat (reap.visit_discount.get opts)
  let priorTemperature := scaledNatToFloat (reap.prior_temperature.get opts)
  let N := node.children.map (fun (e, _) => e.visit) |>.sum
  -- exploration factor
  let c := cInit + Float.log ((N.toFloat + cBase + 1) / cBase)
  return node.children.map fun (e, n) =>
    if let .ok nodeState := n then
      Float.exp (-visitDiscount * (nodeState.value + 1)) +
        c * Float.pow e.prior priorTemperature * N.toFloat.sqrt / (e.visit.toFloat + 1)
    else
      -Float.inf

def selectChild (node : NodeType) : TacticM (Option Nat) := do
  let scores ← computeScores node
  -- I could not find a convenient way in Std to compute argmax of an array
  return Id.run do
    let mut bestIdx := none
    let mut bestScore := -Float.inf
    for (score, i) in scores.zipIdx do
      if score > bestScore then
        bestIdx := some i
        bestScore := score
    return bestIdx

def updateEdge (e : EdgeData) : EdgeData :=
  {
    e with
      visit := e.visit + 1
  }

def updateNode (node : NodeType) : NodeData :=
  if let .ok nodeState := node.data then
    .ok { nodeState with value := nodeState.value + 1, numVisit := nodeState.numVisit + 1 }
  else
    node.data

structure PPNodeData where
  pp : List String
  value : Float
deriving ToJson

def ppNodeData (node : NodeData) : TacticM PPNodeData := do
  node.restore
  let pp ← (← getUnsolvedGoals).mapM fun g => return toString (← Meta.ppGoal g)
  return ⟨ pp, ← node.priority ⟩

end MCTS

open MCTS in
def reapMCTS (tg : TacGen) (se : StateEval)
    (maxNodes := MCTS.defaultMaxNodes)
    (maxSteps := MCTS.defaultMaxSteps) : TacticM Unit := do
  withCumulativeWallClockTime "reap.wall.mcts.total" do
    let (k, nodes) ← monteCarloTreeSearch
      (fun x => x.isTerminal)
      (expand tg se)
      (fun x => selectChild x)
      (fun _ e _ => return updateEdge e)
      (fun x => return updateNode x)
      (.ok ⟨ (← Tactic.saveState), 0.0, 0 ⟩)
      maxNodes maxSteps

    let ppNodes ← nodes.mapM ppNode
    let info := json%{
      solution : $k,
      nodes : $ppNodes
    }
    communicate info

    if let some k := k then
      let some {data := .ok node, ..} := nodes[k]? | unreachable!
      node.state.restore

  printCumulativeWallClockTimes

end Reap.TreeSearch
