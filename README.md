# Riemann Hypothesis

This is a fresh Lean formalization project for the Riemann hypothesis. All Lean
source files live in [`formalization/`](formalization/). The original
[`Challenge.lean`](formalization/Challenge.lean) records the challenge statements
with `sorry` placeholders.

## Build

Install [elan](https://github.com/leanprover/elan), then run these commands from
the project root.

```sh
lake exe cache get
lake build
```

[`lean-toolchain`](lean-toolchain) pins Lean v4.36.0, and
[`lake-manifest.json`](lake-manifest.json) locks Mathlib v4.36.0 and its
dependencies.
