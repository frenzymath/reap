import Reap

set_option reap.policy_endpoint "http://127.0.0.1:7327/policy/v1"
set_option reap.value_endpoint "http://127.0.0.1:7327/value/v1"
set_option reap.wall_clock_log_path "log/wall_clock.jsonl"
set_option reap.raw_tree_path "log/raw_tree.json"

set_option linter.unusedSimpArgs false

example {m n : Nat} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) :
    n / m ∣ n ∧ n / m < n := by
  reap (strategy := .bestFirst)
