import Reap.Tactic.State

open Reap.TreeSearch

set_option linter.unusedVariables false

example (P : Prop) (h1 h2 : P) : P := by
  run_tac simplifyState
  fail_if_success exact h2
  exact h1

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac simplifyState
  exact And.intro hP hQ

example (α : Type) (x y : α) : x = x := by
  run_tac simplifyState
  have _ : α := y
  rfl
