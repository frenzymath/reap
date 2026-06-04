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

def transTacGen : TacGen := fun _ => do
  return #[
    ("trans b", #[], 1.0),
    ("exact h1", #[], 1.0),
    ("exact h2", #[], 1.0)
  ]

example (a b c : Nat) (h1 : a = b) (h2 : b = c) : a = c := by
  run_tac reapMCTS transTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  run_tac reapMCTS andOrTacGen andOrStateEval (maxNodes := 32) (maxSteps := 32)
