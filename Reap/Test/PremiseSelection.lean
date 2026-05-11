import Lean
import Reap.PremiseSelection.Syntax

set_library_suggestions reapSelector

example (a b : Nat) : a + b = b + a := by
  suggestions
  sorry
