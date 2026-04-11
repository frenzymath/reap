import Reap.Tactic.Syntax

set_option linter.unusedSimpArgs false

example : (a b : Nat) → a = b → b = a := by
  reapBFS
