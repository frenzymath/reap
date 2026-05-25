import Reap.Tactic.Syntax

open Reap.TreeSearch

set_option linter.unusedSimpArgs false

def andOrTacGen : TacGen := fun _ => do
  return #[
    ("constructor", #[], 1.0),
    ("exact hP", #[], 1.0),
    ("exact hQ", #[], 1.0)
  ]

def andOrStateEval : StateEval := fun _ => do
  return 0.0

example : (a b c : Nat) → a = b → b = c → a = c := by
  reapMCTS

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac reapMCTS andOrTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)
