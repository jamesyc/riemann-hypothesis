# Riemann Hypothesis Cleaned

This is a fresh Lean formalization project for the Riemann Hypothesis.

This repo is a proof of the Riemann Hypothesis in Lean. This was done with the use of only GPT-6.2 Sol.

All Lean source files live in [`formalization/`](formalization/). The original [`Challenge.lean`](formalization/Challenge.lean) records the challenge statements with `sorry` placeholders. The independent proof starts in [`Solution.lean`](formalization/Solution.lean). See [`holes.md`](holes.md) for the remaining proof obligations.

Reusable Lean results live in [`formalization/Utilities/`](formalization/Utilities/).
Import an individual module such as `Utilities.SmoothedMangoldtMellin` for smoothed prime sums or `Utilities.SelmerKernel` for continuous restriction kernels.
Use `import Utilities` for the full library. The library depends only on Mathlib.

## Build

Install [elan](https://github.com/leanprover/elan), then run these commands from the project root.

```sh
lake exe cache get
lake build
```

[`lean-toolchain`](lean-toolchain) pins Lean v4.36.0, and [`lake-manifest.json`](lake-manifest.json) locks Mathlib v4.36.0 and its dependencies.
