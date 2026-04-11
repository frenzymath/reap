import Reap.Tactic.Syntax

example : (a b c : Nat) → a = b → b = c → a = c := by
  reapMCTS
