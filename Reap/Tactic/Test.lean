import Reap.Tactic.Syntax
import Reap.Tactic.Search

example : (a b : Nat) → a = b → b = a := by
  intros a b h
  rw [h]

example : (a b c : Nat) → a = b → b = c → a = c := by
  intro a b c a_1 a_2
  subst a_1 a_2
  rfl
