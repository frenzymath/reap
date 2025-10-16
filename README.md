# Reap Tactic

https://github.com/user-attachments/assets/39c09672-ecd5-478f-be81-1b5d043c804a

Use `reap` tactic to leverage the power of LLM in your formal proof.

## Introduction

The `reap` tactic take advantages of our latest algebra & research level stepwise-prover [Real-Prover](https://arxiv.org/abs/2505.20613) to facilitate the proof-writing process.

## Installation

To use `reap` in your project, just add a line to `lakefile.lean` or `lakefile.toml`. Please make sure `reap` is added **before `mathlib` dependency** to avoid cache issues.

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

Currently, our model is trained with Mathlib at `v4.16.0`, and `reap` is compatible with up to `v4.24.0`. As we are working on bridging version gap and further improvements, any feedbacks are welcomed.

## Usage

### One-step suggestion

To use the tactic, you need to import the module:

```lean4
import Mathlib
import Reap

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  reap?
```

Here, `reap?` will toggle a `trythis` block, which suggests a possible next step.

There are also some variants of the `reap` tactic:

- `reap` tries to push the goal one step further.
- `reap!` tries to close the goal within a single step, otherwise it will fail.

### Proof search

To do proof search with `reap`:

```lean4
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star

import Reap

theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
  -- This can be solved by `reap!!`
  reap!!
```

Here, `reap!!` take advantage of `aesop.tacGen` interface to do proof search with `reap`.

### Premise selection

`reap` comes with a powerful premise selection engine, named `LeanSearch-PS`, which is trained on Mathlib and augmented corpus. We adapt this engine to work with official `PremiseSelection` interface, to get access:

```lean4
import Mathlib
import Reap

-- Set `reap` as the default premise selector
set_premise_selector reapSelector

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  suggest_premises
```

## Privacy

As `reap` relies on a backend LLM service to provide tactic suggestions, we understand that privacy is a major concern for users. Here are some key points regarding data handling and privacy:

* **Which LLM is used / who runs it?**
  The backend uses our own trained model named **REAL-Prover**. The 7B version is open-sourced on HuggingFace ([link](https://huggingface.co/FrenzyMath/REAL-Prover)), while the hosted version we provide runs on our research cluster.
  
* **Does it require internet access?**
  By default, yes — the default endpoint is our hosted cluster. However, you can override this by setting `tacticgenerator.llm_endpoint` to a locally served instance of REAL-Prover. In that case, no internet connection is needed.
  
* **What API calls are made?**
  When you call `reap` to generate the next tactic, it sends the *current proof state* to the model endpoint you’ve configured (by default, our hosted cluster).
  
* **What data is sent?**

  Only the proof state at the point of the call. No file paths, user identifiers, or other project metadata are transmitted. On our side, this data is processed statelessly by the model.
