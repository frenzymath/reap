import Reap.Tactic.Syntax

open Lean Meta Elab Tactic
open Reap.TreeSearch

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
    ("trans", #[], 1.0),
    ("exact h1", #[], 1.0),
    ("exact h2", #[], 1.0)
  ]

def badTransTacGen : TacGen := fun _ => do
  return #[
    ("trans", #[], 1.0),
    ("rfl", #[], 1.0)
  ]

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

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  run_tac reapMCTS transTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac reapMCTS andOrTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)

example (a b : Nat) : a = a := by
  run_tac guardMCTSNoSolution badTransTacGen andOrStateEval 32 32
  rfl
