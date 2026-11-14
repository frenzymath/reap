import Reap

/-!
End-to-end test of `reap` against live policy and value services.

Requires a running Reaper-1 server (see `reaper-local/serve.py`) at the endpoints
below. Run with `lake env lean Reap/IntegrationTest.lean`. The file fails to
elaborate if search does not find a proof or the services are unreachable.

`reap?` reports its script only through the InfoView widget, so the command line
never sees it. `reapPrint` runs the same search and proof-script check as `reap?`,
logs the script, and then closes the goal with it.
-/

set_option reap.policy_endpoint "http://127.0.0.1:8000/policy/v1"
set_option reap.value_endpoint "http://127.0.0.1:8000/value/v1"

-- Proofs found by search may pass simp arguments the linter cannot match up.
set_option linter.unusedSimpArgs false

-- The example from the README: needs a split plus two library lemmas with side conditions.
theorem reapIntegrationDivDvd {m n : Nat} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) :
    n / m ∣ n ∧ n / m < n := by
  reap
