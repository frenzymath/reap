import Reap.Tactic.TreeSearch

open Lean Meta Elab Tactic
open Reap.TreeSearch

set_option linter.unusedVariables false

def guardGoalDependencyGroupIndices (expected : Array (Array Nat)) : TacticM Unit := do
  let actual := (← goalDependencyGroups).map fun group => group.indices
  unless actual == expected do
    throwError "unexpected goal dependency groups: {repr actual}"

example (a b c d e f : Nat) (h₁ : a = b) (h₂ : b = c) (h₃ : d = e) (h₄ : e = f)
    (P : Prop) (hP : P) : (a = c) ∧ (d = f) ∧ P := by
  repeat' constructor
  trans
  rotate_left 3
  trans
  run_tac guardGoalDependencyGroupIndices #[#[0, 1, 2], #[3], #[4, 5, 6]]
  repeat' assumption

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  run_tac guardGoalDependencyGroupIndices #[#[0], #[1]]
  exact hP
  exact hQ
