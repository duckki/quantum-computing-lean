# Quantum Computing in Lean

A Lean 4 formalization of basic quantum computing definitions.

It is a Lake/mathlib4 project and starts with a small core API for finite-dimensional
complex matrices, state vectors, common qubit states and gates, projections, and
measurement probabilities.

## Requirements

This project is pinned to Lean `v4.29.1` and mathlib4 `v4.29.1`. Lake reads the
Lean version from `lean-toolchain` and the mathlib dependency from
`lakefile.lean`.

## Build

```sh
lake exe cache get
lake build
```

## Using the Library

The top-level module imports the public quantum computing API:

```lean
import QuantumComputing

#check QuantumComputing.ketPlus
#check QuantumComputing.H
#check QuantumComputing.Theorems.NoCloning.no_cloning_1
```

You can also import focused modules when working on a smaller part of the
library:

```lean
import QuantumComputing.Gates
import QuantumComputing.Measurement
import QuantumComputing.Theorems.NoCloning
```

## Highlights

- Finite-dimensional complex matrix and vector API, including adjoint,
  multiplication, trace, projection, Kronecker product, normalization, and
  unitarity facts.
- Named one- and two-qubit states, gates, and projectors, with verified gate
  actions and standard decomposition identities.
- Computational, generalized, projective, and partial-trace measurement APIs.
- Typed circuit syntax with denotational semantics and unitary circuit wrappers.
- Formalized examples including Hadamard-based uniform random-number generation
  and no-cloning theorems.

## Layout

- `QuantumComputing/Matrix.lean`: core finite complex matrix/vector API, adjoint,
  multiplication, trace, projection, Kronecker product support, and
  `Vector.IsNormalized`.
- `QuantumComputing/States.lean`: named state vectors such as `ket0`, `ketPlus`, and
  Bell states, plus their basic state-vector facts.
- `QuantumComputing/Gates.lean`: public gate API.
- `QuantumComputing/Gates/Basic.lean`: named gates such as `X`, `H`, `CNOT`, `CZ`, and
  `SWAP`.
- `QuantumComputing/Gates/Projectors.lean`: named projectors such as `P0`, `P1`,
  `PPlus`, and `PMinus`.
- `QuantumComputing/Gates/Properties.lean`: unitarity, adjoint, and involution facts for
  named gates.
- `QuantumComputing/Gates/Actions.lean`: gate actions on named states.
- `QuantumComputing/Gates/Decompositions.lean`: standard gate decomposition identities.
- `QuantumComputing/State.lean`: pure-state and density-matrix wrappers, including
  mathlib-backed positive semidefiniteness for density matrices.
- `QuantumComputing/Measurement.lean`: public measurement API.
- `QuantumComputing/Measurement/Computational.lean`: computational-basis measurement
  definitions and reusable probability/projector facts.
- `QuantumComputing/Measurement/Generalized.lean`: complete generalized
  measurements and typed generalized measurement operators.
- `QuantumComputing/Measurement/Projective.lean`: projective measurements and
  their bridge to generalized measurements.
- `QuantumComputing/Measurement/PartialTrace.lean`: partial trace and partial
  measurement probability facts.
- `QuantumComputing/Measurement/Examples.lean`: concrete measurement and partial-trace
  facts for named states.
- `QuantumComputing/Circuit/Register.lean`: `n`-qubit register aliases and tensoring with
  the `2 ^ (n + m)` dimension reindexing handled internally.
- `QuantumComputing/Circuit.lean`: typed circuit syntax, denotational semantics, and
  unitary circuit composition.
- `QuantumComputing/Circuit/Examples.lean`: standard unitary circuits and the Bell-state
  preparation example.
- `QuantumComputing.lean`: top-level import module.

## Lean 3 History

The `main` branch is the Lean 4 version of this project. The previous Lean 3
project is preserved for reference on the historical `lean3` branch.

This Lean 4 version is a redesign rather than a line-by-line translation. See
[docs/porting-from-lean3.md](docs/porting-from-lean3.md) for the porting
coverage matrix, intentionally unported Lean 3 infrastructure, and future
cleanup ideas.

## References

- [Quantum Programming tutorial](https://sites.google.com/ncsu.edu/qc-tutorial/home)
- [An Introduction to Quantum Computing, Without the Physics](https://arxiv.org/abs/1708.03684)
- [Verified Quantum Computing](https://www.cs.umd.edu/~rrand/vqc/)

## Related Projects

- [Lean Theorem Prover](https://lean-lang.org)
- [Lean Community](https://leanprover-community.github.io)
- [QWIRE](https://github.com/inQWIRE/QWIRE): a quantum circuit language and
  formal verification tool by Robert Rand et al.
