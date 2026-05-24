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

- `Quantum/Matrix.lean`: core finite complex matrix/vector API, adjoint,
  multiplication, trace, projection, and Kronecker product support.
- `Quantum/Basic.lean`: common states, gates, controlled gates, partial trace,
  and measurement definitions.
- `Quantum/State.lean`: pure-state and density-matrix wrappers, including
  mathlib-backed positive semidefiniteness for density matrices.
- `Quantum/Measurement.lean`: complete generalized measurements and typed
  measurement operators.
- `Quantum/Register.lean`: `n`-qubit register aliases and tensoring with the
  `2 ^ (n + m)` dimension reindexing handled internally.
- `Quantum/Circuit.lean`: typed circuit syntax, denotational semantics, and
  unitary circuit composition.
- `Quantum/Examples.lean`: standard unitary circuits and the Bell-state
  preparation example.
- `Quantum/Core.lean`, `Quantum/States.lean`, `Quantum/Projectors.lean`,
  `Quantum/Gates.lean`, `Quantum/PartialTrace.lean`, and
  `Quantum/Measurement/Lemmas.lean`: reusable theorem modules grouped by the
  definitions they support.
- `Quantum.lean`: top-level import module.
