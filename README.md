# Reap Tactic

Use `reap` tactic to leverage the power of neural prover in your formal proof.

<video controls src="https://github.com/user-attachments/assets/9ca983ea-24bb-4b84-a676-919431787ac1" width="100%"></video>

## Introduction

The `reap` tactic extends our algebra & research level step-prover [Real-Prover](https://arxiv.org/abs/2505.20613) into a unified framework for proof-writing and training rollouts.

## Installation

### Using `reap` as a separate dependency

To use `reap` in your project separately, add a line to `lakefile.lean` or `lakefile.toml`. Please make sure `reap` is added **before `mathlib` dependency** to avoid cache issues.

If you are using `lakefile.lean`, replace

```lean4
require "leanprover-community" / "mathlib"
```

with

```lean4
require "reap" from git "https://github.com/frenzymath/reap.git" @ "main"
require "leanprover-community" / "mathlib"
```

Or if you are using `lakefile.toml`

replace

```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
```

with

```toml
[[require]]
name = "reap"
git = "https://github.com/frenzymath/reap.git"
rev = "main"

[[require]]
name = "mathlib"
scope = "leanprover-community"
```

Currently, our model is trained with Mathlib at `v4.28.0-rc1`, and `reap` is compatible with up to `v4.30.0`. As we are working on bridging version gap and further improvements, any feedbacks are welcomed.

### Using our mathlib4 fork

If you are working on `mathlib4` master or newer, you may use our fork of `mathlib4` which includes `reap` as a dependency. This is the recommended way to use `reap` as it ensures compatibility with the latest features and improvements.

## Usage

### Proof search TryThis

To do proof search with `reap`:

```lean4
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star

import Reap

set_option reap.policy_endpoint "<policy_endpoint>"
set_option reap.value_endpoint "<value_endpoint>"
set_option reap.ps_endpoint "<premise_selection_endpoint>"

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  -- This asks Reap to search and suggest a proof.
  reap!!
```

Here, `reap!!` runs Reap's MCTS proof search using the policy, value, and premise-selection services, then displays the assembled proof as a TryThis block. It does not replace the tactic automatically; use the `[apply]` link in the InfoView to insert the suggested proof.

### RL interface

For RL rollouts, `reapMCTS` runs the current MCTS search: it expands Lean proof
states with policy-generated tactics, uses the value model to guide exploration,
checks each step in Lean, and replays the proof when a solution is found.

`reap!!` runs the same rollout asynchronously with UI reporting. Progress is shown in the Lean
InfoView as the "Reap MCTS progress" widget, with search status, step count, and
current goal type. If a proof is found, the rollout result is shown there as a
TryThis block with an `[apply]` link.

Optional file outputs can be enabled with:

```lean4
set_option reap.wall_clock_log_path "reap_wall_clock.jsonl"
set_option reap.raw_tree_path "reap_mcts_tree.json"
```

`reap.wall_clock_log_path` appends JSONL timing records for premise selection,
tactic generation, value calls, and tactic evaluation. `reap.raw_tree_path`
writes the final raw MCTS tree, including the solution node and explored nodes.

### Premise selection

`reap` comes with a powerful premise selection engine, named `LeanSearch-PS`, which is trained on Mathlib and augmented corpus. We adapt this engine to work with official library suggestions interface, to get access:

```lean4
import Mathlib
import Reap

-- Set `reap` as the default premise selector
set_library_suggestions reapSelector

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  suggestions
```

## Privacy

As `reap` relies on a backend LLM service to provide tactic suggestions, we understand that privacy is a major concern for users. Here are some key points regarding data handling and privacy:

* **Which LLM is used / who runs it?**
  The backend uses our trained model named **REAL-Prover**. The 7B version is open-sourced on HuggingFace ([link](https://huggingface.co/FrenzyMath/REAL-Prover)); configure `reap.policy_endpoint`, `reap.value_endpoint`, and `reap.ps_endpoint` for the services you want to use.

* **Does it require internet access?**
  Only if the endpoints you configure are remote services. You can set the endpoint options to locally served instances; in that case, no internet connection is needed.

* **What API calls are made?**
  When you call `reap` to generate the next tactic, it sends the *current proof state* to the model endpoint you have configured.

* **What data is sent?**

  Only the proof state at the point of the call. No file paths, user identifiers, or other project metadata are transmitted. On our side, this data is processed statelessly by the model.
