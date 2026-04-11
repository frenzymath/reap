import Reap.Tactic.Syntax

set_option linter.unusedSimpArgs false

example : (a b c : Nat) → a = b → b = c → a = c := by
  reapMCTS
