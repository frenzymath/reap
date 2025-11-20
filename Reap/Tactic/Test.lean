import Reap.Tactic.Syntax
import Reap.Tactic.Search

example : (a b : Nat) → a = b → b = a := by
  reap!!

example : (a b c : Nat) → a = b → b = c → a = c := by
  reap!!
