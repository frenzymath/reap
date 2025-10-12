import Lean
import Reap.PremiseSelection.Syntax

set_premise_selector reapSelector

example (a b : Nat) : a + b = b + a := by
  suggest_premises
  sorry
