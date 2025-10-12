import Reap.Tactic.Syntax
import Reap.Tactic.Search

example : (a b : Nat) → a = b → b = a := by
  intro a b h
  subst h
  simp_all only

example : (a b c : Nat) → a = b → b = c → a = c := by
  intro a b c a_1 a_2
  subst a_2 a_1
  rfl
