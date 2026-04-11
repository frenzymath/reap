import Reap.Tactic.Syntax

example : (a b : Nat) → a = b → b = a := by
  reapBFS
