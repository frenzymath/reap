import Reap.Tactic.Syntax
import Reap.Tactic.TreeSearch

example : (a b : Nat) → a = b → b = a := by
  reapBFS

example : (a b c : Nat) → a = b → b = c → a = c := by
  reapMCTS
