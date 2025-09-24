# Reap Tactic

https://github.com/user-attachments/assets/39c09672-ecd5-478f-be81-1b5d043c804a

Use `reap` tactic to leverage the power of LLM in your formal proof.

## Introduction

The `reap` tactic take advantages of our latest algebra & research level stepwise-prover [Real-Prover](https://arxiv.org/abs/2505.20613) to facilitate the proof-writing process.


## Installation

To use `reap` in your project, just add a line to `lakefile.lean` or `lakefile.toml`.

If you are using `lakefile.lean`, add the following line to your repo.

```lean4
require "reap" from git "https://github.com/frenzymath/reap.git"
```
Or if you are using `lakefile.toml`

```toml
[[require]]
name = "reap"
git = "https://github.com/frenzymath/reap.git"
rev = "main"
```

Currently, our model works best with Mathlib binded with `v4.16.0`, you can also test it on other versions. Any feedbacks are welcomed.

## Usage

To use the tactic, you need to import the module:

```lean4
import Mathlib
import Reap

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  reap?
```

There are also some variants of the `reap` tactic:

- `reap` tries to push the goal one step further.
- `reap!` tries to close the goal within a single step, otherwise it will fail.
- `reap?` generates the tactic and then toggles a `trythis` block, allowing you to manually specify the next step.




