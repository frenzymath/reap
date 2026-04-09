module
public meta import Lean
public meta import TreeSearch.BestFirst
public meta import TreeSearch.MCTS
open Lean Meta Elab Tactic TreeSearch

public meta section

namespace Reap.TreeSearch

register_option reap.heartbeats : Nat := {
  defValue := 1000000000
  descr := "Maximum heartbeats per tactic"
}

def withHeartbeats {m : Type _ → Type _} {α : Type _} [Monad m] [MonadWithReaderOf Core.Context m] (heartbeats : Nat) : m α → m α :=
  withReader (fun s => { s with maxHeartbeats := heartbeats })

def evalTacticStr (str : String) (heartbeats : Nat) : TacticM (Option Tactic.SavedState) := do
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

def isTerminal (ss : Tactic.SavedState) : TacticM Bool := do
  ss.restore
  return (← getUnsolvedGoals).isEmpty

abbrev TacGen := List MVarId → MetaM (Array (String × Float))
abbrev StateEval := List MVarId → MetaM Float

namespace BFS

structure SearchState where
  valid : Bool
  state : Tactic.SavedState
  priority : Float := 0.0

def priority (ss : SearchState) : TacticM Float := do
  if ← isTerminal ss.state then
    return Float.inf
  else
    return ss.priority

def expand (tg : TacGen) (se : Option StateEval) (ss : SearchState) : TacticM (Array (String × SearchState)) :=
  if not ss.valid then
    return #[]
  else do
    let p := ss.priority
    ss.state.restore
    let tactics ← tg (← getUnsolvedGoals)
    tactics.mapM fun (t, Δp) => do
      ss.state.restore
      if let some s' ← evalTacticStr t (reap.heartbeats.get (← getOptions)) then
        -- TODO: merge nodes
        s'.restore
        let g ← getUnsolvedGoals
        let p' ← if g.isEmpty then
          pure Float.inf
        else if let some se := se then
          se g
        else
          pure (p + Δp)
        return (t, ⟨ true, s', p' ⟩)
      else
        return (t, ⟨ false, ss.state, -Float.inf ⟩)

structure PPSearchState where
  valid : Bool
  pp : List String
  priority : Float
deriving ToJson

def ppSearchState (ss : SearchState) : TacticM PPSearchState := do
  ss.state.restore
  let pp ← (← getUnsolvedGoals).mapM fun g => return toString (← Meta.ppGoal g)
  return ⟨ ss.valid, pp, ss.priority ⟩
end BFS

open BFS in
/--
TODO: For now, `proofSearchBFS` is exposed to the root namespace
so that we don't need to make any changes in the reap repository.
In the future, we may want to move it to a more appropriate namespace.
-/
def proofSearchBFS (tg : TacGen) (se : Option StateEval)
    (maxNodes := BestFirst.defaultMaxNodes) : TacticM Unit := do
  let (k, nodes) ← bestFirstSearch priority (fun x => isTerminal x.state)
    (expand tg se) ⟨ true, ← Tactic.saveState, 0.0 ⟩ maxNodes
  let ppNodes ← nodes.mapM fun node => do
    let pp ← ppSearchState node.data
    return json%{
      state: $pp,
      children: $(node.children)
    }
  let info := json%{
    solution: $k,
    nodes: $ppNodes
  }

  -- Do something with the JSON data
  IO.println info

  if let some k := k then
    let some node := nodes[k]? | unreachable!
    node.data.state.restore


namespace MCTS

structure NodeData where
  state : Tactic.SavedState
  value : Float

structure EdgeData where
  tacticStr : String
  prior : Float
  visit : Nat := 0
deriving ToJson

abbrev NodeType := Node NodeData (EdgeData × NodeData)

def expand (tg : TacGen) (se : StateEval) (node : NodeType) : TacticM (Array (EdgeData × NodeData)) := do
  let s₀ := node.data.state
  let mut ret := #[]
  s₀.restore
  let tactics ← tg (← getUnsolvedGoals)
  for (t, p) in tactics do
    s₀.restore
    if let some s' ← evalTacticStr t (reap.heartbeats.get (← getOptions)) then
      s'.restore
      -- TODO: figure out initialization of nodes
      ret := ret.push (⟨ t, p, 0 ⟩, ⟨ s', ← se (← getUnsolvedGoals) ⟩)
  return ret

def c_base := 1.0
def c_init := 0.0
def gamma := 1.0
def temperature := 1.0

def computeScores (node : NodeType) : Array Float :=
  let N := node.children.map (fun (e, _) => e.visit) |>.sum
  -- exploration factor
  let c := c_init + Float.log ((N.toFloat + c_base + 1) / c_base)
  node.children.map fun (e, n) =>
    Float.exp (-gamma * (n.value + 1)) +
      c * Float.pow e.prior temperature * N.toFloat.sqrt / (e.visit.toFloat + 1)

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
  {
    node.data with
      value := node.data.value + 1
  }

structure PPNodeData where
  pp : List String
  value : Float
deriving ToJson

def ppNodeData (node : NodeData) : TacticM PPNodeData := do
  node.state.restore
  let pp ← (← getUnsolvedGoals).mapM fun g => return toString (← Meta.ppGoal g)
  return ⟨ pp, node.value ⟩

end MCTS

open MCTS in
def reapMCTS (tg : TacGen) (se : StateEval)
    (maxNodes := MCTS.defaultMaxNodes)
    (maxSteps := MCTS.defaultMaxSteps) : TacticM Unit := do
  let (k, nodes) ← monteCarloTreeSearch
    (fun x => isTerminal x.state)
    (expand tg se)
    (fun x => return selectChild x)
    (fun _ e _ => return updateEdge e)
    (fun x => return updateNode x)
    ⟨ ← Tactic.saveState, 0.0 ⟩
    maxNodes maxSteps

  let ppNodes ← nodes.mapM fun node => do
    let pp ← ppNodeData node.data
    return json%{
      state: $pp,
      children: $(node.children)
    }
  let info := json%{
    solution: $k,
    nodes: $ppNodes
  }

  -- Do something with the JSON data
  IO.println info

  if let some k := k then
    let some node := nodes[k]? | unreachable!
    node.data.state.restore

end Reap.TreeSearch
