import Reap.Tactic.Syntax

open Lean Meta Elab Tactic
open Reap.TreeSearch
open TreeSearch

set_option linter.unusedSimpArgs false

def andOrPolicyValue : PolicyValueEval := fun _ => do
  return (0.0, #[
    ("constructor", #[], 1.0),
    ("exact hP", #[], 1.0),
    ("exact hQ", #[], 1.0)
  ])

def transPolicyValue : PolicyValueEval := fun _ => do
  return (0.0, #[
    ("trans b", #[], 1.0),
    ("exact h1", #[], 1.0),
    ("exact h2", #[], 1.0)
  ])

def existsPolicyValue : PolicyValueEval := fun _ => do
  return (0.0, #[
    ("constructor", #[], 1.0),
    ("exact 0", #[], 1.0),
    ("rfl", #[], 1.0)
  ])

def selfLoopPolicyValue : PolicyValueEval := fun _ => do
  return (0.0, #[
    ("skip", #[], 1.0),
    ("trivial", #[], 1.0)
  ])

def hasLocalDeclNamed (goals : List MVarId) (name : Name) : MetaM Bool := do
  let some goal := goals.head? | return false
  goal.withContext do
    for localDecl in ← getLCtx do
      if localDecl.userName == name then
        return true
    return false

def ancestorLoopPolicyValue : PolicyValueEval := fun goals => do
  if ← hasLocalDeclNamed goals `h then
    return (0.0, #[
      ("clear h", #[], 1.0),
      ("exact True.intro", #[], 1.0)
    ])
  else
    return (0.0, #[
      ("have h : True := by trivial", #[], 1.0),
      ("have h : True := by trivial", #[], 1.0)
    ])

def deferredHavePolicyValue (unfocusedVisits : IO.Ref Nat) : PolicyValueEval := fun goals => do
  if ← hasLocalDeclNamed goals `h then
    return (0.0, #[("exact h", #[], 1.0)])
  let visits ← unfocusedVisits.get
  unfocusedVisits.set (visits + 1)
  if visits == 0 then
    return (0.0, #[("have h : P := ?_", #[], 1.0)])
  else
    return (0.0, #[("exact hP", #[], 1.0)])

def runMCTSForTest (evalPolicyValue : PolicyValueEval) (maxNodes := 32) (maxSteps := 32) :
    TacticM (Option Nat × Array (Node MCTS.NodeData (MCTS.EdgeData × Nat))) := unsafe do
  let ctx ← mkProofCheckContext
  let params := SearchHyperparameters.fromOptions (← getOptions)
  MCTS.monteCarloTreeSearch ctx evalPolicyValue params (← MCTS.NodeData.fromState) maxNodes maxSteps

def childTacticStrings (node : Node MCTS.NodeData (MCTS.EdgeData × Nat)) : Array String :=
  node.children.map fun (edge, _) => edge.tacticStr

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  run_tac do
    let kind ← MCTS.childKindAfterTactic
    unless kind == .andNode do
      throwError "expected constructor on conjunction to create an AND node"
  · exact hP
  · exact hQ

example : ∃ n : Nat, n = n := by
  constructor
  run_tac do
    let kind ← MCTS.childKindAfterTactic
    unless kind == .orNode do
      throwError "expected constructor on existential with metavariable goals to stay an OR node"
  · rfl
  · exact 0

example : True := by
  run_tac do
    let (_, nodes) ← runMCTSForTest selfLoopPolicyValue (maxNodes := 8) (maxSteps := 8)
    let some root := nodes[0]? | unreachable!
    let tactics := childTacticStrings root
    if tactics.contains "skip" then
      throwError "expected ancestor self-loop tactic to be dropped"
    unless tactics.contains "trivial" do
      throwError "expected non-loop solving tactic to remain"

example : True := by
  run_tac do
    let (_, nodes) ← runMCTSForTest ancestorLoopPolicyValue (maxNodes := 8) (maxSteps := 8)
    let some root := nodes[0]? | unreachable!
    unless root.children.size == 1 do
      throwError "expected duplicate non-loop child states to merge"
    let some (rootEdge, childIdx) := root.children[0]? | unreachable!
    unless rootEdge.tacticStr == "have h : True := by trivial" do
      throwError "unexpected root tactic after duplicate merge: {rootEdge.tacticStr}"
    unless rootEdge.probability > 1.9 do
      throwError "expected duplicate child prior mass to be merged"
    let some child := nodes[childIdx]? | unreachable!
    let tactics := childTacticStrings child
    if tactics.contains "clear h" then
      throwError "expected depth ancestor-loop tactic to be dropped"
    unless tactics.contains "exact True.intro" do
      throwError "expected non-loop child solving tactic to remain"

example (P : Prop) (hP : P) : P := by
  run_tac do
    let saved ← saveState
    let unfocusedVisits ← IO.mkRef 0
    let (some _, nodes) ← runMCTSForTest (deferredHavePolicyValue unfocusedVisits)
        (maxNodes := 32) (maxSteps := 32)
      | throwError "expected MCTS to solve deferred have proof"
    unless nodes.any (fun node => node.children.any fun (edge, _) => edge.tacticStr == "exact h") do
      throwError "expected MCTS to accept delayed final-check child tactic"
    saved.restore
    let replayVisits ← IO.mkRef 0
    reapMCTS (deferredHavePolicyValue replayVisits) (maxNodes := 32) (maxSteps := 32)

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  run_tac reapMCTS transPolicyValue (maxNodes := 32) (maxSteps := 32)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac reapMCTS andOrPolicyValue (maxNodes := 32) (maxSteps := 32)

example : ∃ n : Nat, n = n := by
  run_tac reapMCTS existsPolicyValue (maxNodes := 32) (maxSteps := 32)
