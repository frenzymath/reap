# Reap Tactic

https://github.com/user-attachments/assets/39c09672-ecd5-478f-be81-1b5d043c804a

Use `reap` tactic to leverage the power of LLM in your formal proof.

## Introduction

The `reap` tactic take advantages of our latest algebra & research level stepwise-prover [Real-Prover](https://arxiv.org/abs/2505.20613) to facilitate the proof-writing process.


## Installation

Just add a line to `lakefile.lean` or `lakefile.toml` to require the package.

```lean4
require "reap" from git "https://github.com/frenzymath/reap.git"
```

## Usage

To use the tactic, you need to import the module:

```lean4
import Reap

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  reap
```

There are also some variants of the `reap` tactic that you can use:

- `reap!` tries to close the goal within a single step, otherwise it will fail.
- `reap?` generates the tactic and then toggles a `trythis` block, allowing you to manually specify the next step.


