# Quantum

A Lean 4 formalization of basic quantum computing definitions.

It is a Lake/mathlib4 project and starts with a small core API for finite-dimensional
complex matrices, state vectors, common qubit states and gates, projections, and
measurement probabilities.

## Build

```sh
lake exe cache get
lake build
```

## Layout

- `Quantum/Matrix.lean`: core finite complex matrix/vector API, adjoint,
  multiplication, trace, projection, Kronecker product support, and
  `Vector.IsNormalized`.
- `Quantum/States.lean`: named state vectors such as `ket0`, `ketPlus`, and
  Bell states, plus their basic state-vector facts.
- `Quantum/Gates.lean`: public gate API.
- `Quantum/Gates/Basic.lean`: named gates such as `X`, `H`, `CNOT`, `CZ`, and
  `SWAP`.
- `Quantum/Gates/Projectors.lean`: named projectors such as `P0`, `P1`,
  `PPlus`, and `PMinus`.
- `Quantum/Gates/Properties.lean`: unitarity, adjoint, and involution facts for
  named gates.
- `Quantum/Gates/Actions.lean`: gate actions on named states.
- `Quantum/Gates/Decompositions.lean`: standard gate decomposition identities.
- `Quantum/State.lean`: pure-state and density-matrix wrappers, including
  mathlib-backed positive semidefiniteness for density matrices.
- `Quantum/Measurement.lean`: public measurement API.
- `Quantum/Measurement/Computational.lean`: computational-basis measurement
  definitions and reusable probability/projector facts.
- `Quantum/Measurement/Generalized.lean`: complete generalized
  measurements and typed generalized measurement operators.
- `Quantum/Measurement/Projective.lean`: projective measurements and
  their bridge to generalized measurements.
- `Quantum/Measurement/PartialTrace.lean`: partial trace and partial
  measurement probability facts.
- `Quantum/Measurement/Examples.lean`: concrete measurement and partial-trace
  facts for named states.
- `Quantum/Circuit/Register.lean`: `n`-qubit register aliases and tensoring with
  the `2 ^ (n + m)` dimension reindexing handled internally.
- `Quantum/Circuit.lean`: typed circuit syntax, denotational semantics, and
  unitary circuit composition.
- `Quantum/Circuit/Examples.lean`: standard unitary circuits and the Bell-state
  preparation example.
- `Quantum.lean`: top-level import module.

## Lean 3 Porting Notes

The Lean 4 branch is a redesign rather than a line-by-line translation of the
Lean 3 `master` branch. See
[docs/porting-from-lean3.md](docs/porting-from-lean3.md) for the current
coverage matrix, intentionally unported Lean 3 infrastructure, and remaining
candidate work.
