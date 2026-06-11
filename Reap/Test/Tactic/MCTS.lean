import Reap.Tactic.Syntax

open Lean Meta Elab Tactic
open Reap.TreeSearch
open TreeSearch

set_option linter.unusedSimpArgs false

def andOrTacGen : TacGen := fun _ => do
  return #[
    ("constructor", #[], 1.0),
    ("exact hP", #[], 1.0),
    ("exact hQ", #[], 1.0)
  ]

def andOrStateEval : StateEval := fun _ => do
  return 0.0

def transTacGen : TacGen := fun _ => do
  return #[
    ("trans b", #[], 1.0),
    ("exact h1", #[], 1.0),
    ("exact h2", #[], 1.0)
  ]

def existsTacGen : TacGen := fun _ => do
  return #[
    ("constructor", #[], 1.0),
    ("exact 0", #[], 1.0),
    ("rfl", #[], 1.0)
  ]

def selfLoopTacGen : TacGen := fun _ => do
  return #[
    ("skip", #[], 1.0),
    ("trivial", #[], 1.0)
  ]

def hasLocalDeclNamed (goals : List MVarId) (name : Name) : MetaM Bool := do
  let some goal := goals.head? | return false
  goal.withContext do
    for localDecl in ← getLCtx do
      if localDecl.userName == name then
        return true
    return false

def ancestorLoopTacGen : TacGen := fun goals => do
  if ← hasLocalDeclNamed goals `h then
    return #[
      ("clear h", #[], 1.0),
      ("exact True.intro", #[], 1.0)
    ]
  else
    return #[
      ("have h : True := by trivial", #[], 1.0),
      ("have h : True := by trivial", #[], 1.0)
    ]

def usedPremiseTacGen : TacGen := fun _ => do
  return #[
    ("exact Nat.succ_eq_add_one 0", #[], 1.0)
  ]

def complexUsedPremiseTacGen : TacGen := fun _ => do
  return #[
    ("exact Eq.trans (Nat.succ_eq_add_one 0) h", #[], 1.0)
  ]

def runMCTSForTest (tg : TacGen) (maxNodes := 32) (maxSteps := 32) :
    TacticM (Option Nat × Array (Node MCTS.NodeData (MCTS.EdgeData × Nat))) := unsafe do
  let ctx ← mkProofCheckContext
  let params := SearchHyperparameters.fromOptions (← getOptions)
  MCTS.monteCarloTreeSearch ctx tg andOrStateEval params (← MCTS.NodeData.fromState) maxNodes maxSteps

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
    let (_, nodes) ← runMCTSForTest selfLoopTacGen (maxNodes := 8) (maxSteps := 8)
    let some root := nodes[0]? | unreachable!
    let tactics := childTacticStrings root
    if tactics.contains "skip" then
      throwError "expected ancestor self-loop tactic to be dropped"
    unless tactics.contains "trivial" do
      throwError "expected non-loop solving tactic to remain"

example : True := by
  run_tac do
    let (_, nodes) ← runMCTSForTest ancestorLoopTacGen (maxNodes := 8) (maxSteps := 8)
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

example : Nat.succ 0 = 0 + 1 := by
  run_tac do
    let saved ← saveState
    let (_, nodes) ← runMCTSForTest usedPremiseTacGen (maxNodes := 8) (maxSteps := 8)
    saved.restore
    let some root := nodes[0]? | unreachable!
    let some (edge, _) := root.children.find? fun (edge, _) =>
      edge.tacticStr == "exact Nat.succ_eq_add_one 0"
      | throwError "expected used-premise tactic edge"
    unless edge.used_premise.contains `Nat.succ_eq_add_one do
      throwError "expected Nat.succ_eq_add_one in used_premise, got {edge.used_premise}"
  exact Nat.succ_eq_add_one 0

example (h : 0 + 1 = 1) : Nat.succ 0 = 1 := by
  run_tac do
    let saved ← saveState
    let (_, nodes) ← runMCTSForTest complexUsedPremiseTacGen (maxNodes := 8) (maxSteps := 8)
    saved.restore
    let some root := nodes[0]? | unreachable!
    let some (edge, _) := root.children.find? fun (edge, _) =>
      edge.tacticStr == "exact Eq.trans (Nat.succ_eq_add_one 0) h"
      | throwError "expected complex used-premise tactic edge"
    unless edge.used_premise.contains `Eq.trans do
      throwError "expected Eq.trans in used_premise, got {edge.used_premise}"
    unless edge.used_premise.contains `Nat.succ_eq_add_one do
      throwError "expected Nat.succ_eq_add_one in used_premise, got {edge.used_premise}"
    if edge.used_premise.contains `h then
      throwError "expected local hypothesis h to be excluded, got {edge.used_premise}"
  exact Eq.trans (Nat.succ_eq_add_one 0) h

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac do
    let saved ← saveState
    let (_, nodes) ← runMCTSForTest andOrTacGen (maxNodes := 32) (maxSteps := 32)
    saved.restore
    let mut sawFocus := false
    let mut hPEdge? : Option MCTS.EdgeData := none
    for node in nodes do
      for (edge, _) in node.children do
        if edge.isFocus then
          sawFocus := true
          unless edge.used_premise.isEmpty do
            throwError "expected focus edge used_premise to be empty, got {edge.used_premise}"
        if edge.tacticStr == "exact hP" then
          hPEdge? := some edge
    unless sawFocus do
      throwError "expected focus edges in AND-node rollout"
    let some hPEdge := hPEdge? | throwError "expected exact hP edge"
    unless hPEdge.used_premise.isEmpty do
      throwError "expected local hypothesis hP to be excluded, got {hPEdge.used_premise}"
  constructor
  · exact hP
  · exact hQ

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  run_tac reapMCTS transTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac reapMCTS andOrTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)

example : ∃ n : Nat, n = n := by
  run_tac reapMCTS existsTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)
