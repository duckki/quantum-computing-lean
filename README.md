# Quantum

A fresh Lean 4 formalization of basic quantum computing definitions.

This branch intentionally drops the old Lean 3 project structure. The new code is
a Lake/mathlib4 project and starts with a small core API for finite-dimensional
complex matrices, state vectors, common qubit states and gates, projections, and
measurement probabilities.

## Build

```sh
lake exe cache get
lake build
```

## Layout

- `Quantum/Matrix.lean`: core finite complex matrix and vector API.
- `Quantum/Basic.lean`: common states, gates, projections, trace, and
  measurement definitions.
- `Quantum.lean`: top-level import module.
