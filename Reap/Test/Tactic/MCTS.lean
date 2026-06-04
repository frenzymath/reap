import Reap.Tactic.Syntax

open Lean Meta Elab Tactic
open Reap.TreeSearch

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def andOrTacGen : TacGen := fun _ => do
  return #[
    ("exact hP", #[], 1.0),
    ("exact hQ", #[], 1.0),
    ("constructor", #[], 1.0)
  ]

def andOrStateEval : StateEval := fun _ => do
  return 0.0

def transTacGen : TacGen := fun _ => do
  return #[
    ("exact h1", #[], 1.0),
    ("exact h2", #[], 1.0),
    ("trans b", #[], 1.0)
  ]

def badTransTacGen : TacGen := fun _ => do
  return #[
    ("trans b", #[], 1.0),
    ("rfl", #[], 1.0)
  ]

def testMCTSParams : SearchHyperparameters := {
  cBase := 3200.0
  cInit := 0.0
  visitDiscount := 0.99
  priorTemperature := 1.0
  progressiveSamplingC := 0.0
  progressiveSamplingAlpha := 0.0
}

def testEdge (tacticStr : String) (numVisit : Nat := 1) (isFocus : Bool := false) :
    MCTS.EdgeData := {
  tacticStr
  premise := #[]
  probability := 1.0
  value := 0.0
  numVisit
  isFocus
  focusIndices := #[]
}

def guardPUCTStepCostPrefersShorterChild : TacticM Unit := do
  let base ← MCTS.NodeData.fromState
  let parent := { base with numVisit := 10 }
  let shortChild := { base with numVisit := 1, valueSum := 0.0 }
  let longChild := { base with numVisit := 1, valueSum := -2.0 }
  let node : MCTS.NodeType := {
    data := parent
    children := #[
      (testEdge "short", shortChild),
      (testEdge "long", longChild)
    ]
  }
  let scores := MCTS.computePUCTScores testMCTSParams node
  let some (shortScore, _) := scores[0]? | throwError "missing short-child PUCT score"
  let some (longScore, _) := scores[1]? | throwError "missing long-child PUCT score"
  unless shortScore > longScore do
    throwError "expected step cost to make shorter child score higher; short={shortScore}, long={longScore}"

def guardPUCTUnvisitedValueScoreZero : TacticM Unit := do
  let base ← MCTS.NodeData.fromState
  let parent := { base with numVisit := 1 }
  let child := { base with numVisit := 0, valueSum := 0.0 }
  let node : MCTS.NodeType := {
    data := parent
    children := #[(testEdge "new" (numVisit := 0), child)]
  }
  let scores := MCTS.computePUCTScores testMCTSParams node
  let some (_, cqu) := scores[0]? | throwError "missing unvisited-child PUCT score"
  unless cqu.Q == 0.0 do
    throwError "expected unvisited child Q to be 0.0; got {toString cqu.Q}"

def guardFocusEdgeHasNoStepCost : TacticM Unit := do
  let focusEdge := testEdge "focus_goals [0]" (isFocus := true)
  let tacticEdge := testEdge "exact h"
  unless 3.0 - MCTS.edgeStepCost focusEdge == 3.0 do
    throwError "expected focus edge to have zero step cost"
  unless 3.0 - MCTS.edgeStepCost tacticEdge == 2.0 do
    throwError "expected real tactic edge to cost one step"

def guardMCTSNoSolution (tg : TacGen) (se : StateEval) (maxNodes maxSteps : Nat) :
    TacticM Unit := unsafe do
  withoutModifyingState do
    withMainContext do
      let fvars ← getNonAuxFVars
      let some lhs := fvars[0]? | throwError "expected at least two local constants"
      let some rhs := fvars[1]? | throwError "expected at least two local constants"
      let target ← mkAppM ``Eq #[lhs, rhs]
      let mvar ← mkFreshExprMVar (some target)
      setGoals [mvar.mvarId!]
      let ctx ← mkProofCheckContext
      let params := SearchHyperparameters.fromOptions (← getOptions)
      let (k, _) ← MCTS.monteCarloTreeSearch ctx tg se params (← MCTS.NodeData.fromState) maxNodes maxSteps
      if k.isSome then
        throwError "MCTS incorrectly solved a proof by splitting goals with shared metavariables"

example : True := by
  run_tac guardPUCTStepCostPrefersShorterChild
  trivial

example : True := by
  run_tac guardPUCTUnvisitedValueScoreZero
  trivial

example : True := by
  run_tac guardFocusEdgeHasNoStepCost
  trivial

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  run_tac reapMCTS transTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac reapMCTS andOrTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)

example (a b : Nat) : a = a := by
  run_tac guardMCTSNoSolution badTransTacGen andOrStateEval 32 32
  rfl
