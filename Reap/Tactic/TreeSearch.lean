module
public meta import Lean
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

abbrev TacGen := List MVarId → MetaM (Array (String × Float))
abbrev StateEval := List MVarId → MetaM Float

inductive NodeData where
  | error (message : String)
  | ok (state : Tactic.SavedState) (score : Float)

namespace NodeData
def priority : NodeData → TacticM Float
  | .error _ => return Float.inf
  | .ok state score => do
      if ← isSolved state then
        return Float.inf
      else
        return score

def isTerminal : NodeData → TacticM Bool
  | .error _ => pure false
  | .ok state _ => TreeSearch.isSolved state

def restore : NodeData → TacticM Unit
  | .error _ => pure ()
  | .ok state _ => state.restore

end NodeData

def ppNodeData : NodeData → TacticM Json
  | .error message => pure <| json%{ message: $message }
  | .ok state score => do
    state.restore
    let pp ← (← getUnsolvedGoals).mapM fun g => do return toString (← Meta.ppGoal g)
    return json%{
      state: $(pp),
      score: $(score)
    }

def ppNode {ε} [ToJson ε] (node : Node NodeData ε) : TacticM Json := do
  return json%{
    data: $(← ppNodeData node.data),
    children: $(node.children)
  }

namespace BFS
def expand (tg : TacGen) (se : Option StateEval) : NodeData → TacticM (Array (String × NodeData))
  | .error _ => pure #[]
  | .ok state score => do
    state.restore
    let tactics ← tg (← getUnsolvedGoals)
    tactics.mapM fun (t, Δp) => do
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
        return (t, .ok s' p')
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
      (expand tg se) (.ok (← Tactic.saveState) 0.0) maxNodes
    let ppNodes ← nodes.mapM ppNode
    let info := json%{
      solution : $k,
      nodes : $ppNodes
    }
    -- Do something with the JSON data
    IO.println info

    if let some k := k then
      let some {data := .ok state _, ..} := nodes[k]? | unreachable!
      state.restore
  printCumulativeWallClockTimes

end BFS

namespace MCTS

structure EdgeData where
  tacticStr : String
  prior : Float
  visit : Nat := 0
deriving ToJson

abbrev NodeType := Node NodeData (EdgeData × NodeData)

def expand (tg : TacGen) (se : StateEval) (node : NodeType) : TacticM (Array (EdgeData × NodeData)) := do
  if let .ok s₀ _ := node.data then
    let mut ret := #[]
    s₀.restore
    let tactics ← tg (← getUnsolvedGoals)
    for (t, p) in tactics do
      s₀.restore
      if let some s' ← evalTacticStr t (reap.heartbeats.get (← getOptions)) then
        s'.restore
        -- TODO: figure out initialization of nodes
        let score ← se (← getUnsolvedGoals)
        ret := ret.push (⟨ t, p, 0 ⟩, .ok s' score)
      else
        ret := ret.push (⟨ t, 0, 0 ⟩, .error "")

    return ret
  else
    return #[]

def c_base := 1.0
def c_init := 0.0
def gamma := 1.0
def temperature := 1.0

def computeScores (node : NodeType) : Array Float :=
  let N := node.children.map (fun (e, _) => e.visit) |>.sum
  -- exploration factor
  let c := c_init + Float.log ((N.toFloat + c_base + 1) / c_base)
  node.children.map fun (e, n) =>
    if let .ok _ score := n then
      Float.exp (-gamma * (score + 1)) +
        c * Float.pow e.prior temperature * N.toFloat.sqrt / (e.visit.toFloat + 1)
    else
      -Float.inf

def selectChild (node : NodeType) : Option Nat :=
  let scores := computeScores node
  -- I could not find a convenient way in Std to compute argmax of an array
  Id.run do
    let mut bestIdx := none
    let mut bestScore := 0.0
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
  if let .ok state score := node.data then
    .ok state (score + 1)
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
      (fun x => return selectChild x)
      (fun _ e _ => return updateEdge e)
      (fun x => return updateNode x)
      (NodeData.ok (← Tactic.saveState) 0.0)
      maxNodes maxSteps

    let ppNodes ← nodes.mapM ppNode
    let info := json%{
      solution : $k,
      nodes : $ppNodes
    }
    -- Do something with the JSON data
    IO.println info

    if let some k := k then
      let some {data := .ok state _, ..} := nodes[k]? | unreachable!
      state.restore

  printCumulativeWallClockTimes

end Reap.TreeSearch
