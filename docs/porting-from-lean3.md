# Lean 3 to Lean 4 Porting Coverage

This file tracks the remaining gap between the Lean 3 `master` branch and the
Lean 4 `lean4` branch. The goal is not to recreate every Lean 3 helper exactly;
the Lean 4 port should keep declarations that are part of the quantum API, use
mathlib4 where it now provides the infrastructure, and leave obsolete proof
automation behind.

## Coverage Matrix

| Lean 3 area | Lean 4 location | Status | Notes |
| --- | --- | --- | --- |
| `src/common_lemmas.lean` | mathlib4 / local proofs | Replaced | Finite-index and cast helpers are mostly avoided by `finProdFinEquiv`, `Fin` APIs, and direct `simp`/`fin_cases` proofs. Do not port wholesale unless a public theorem needs one. |
| `src/matrix.lean` | `QuantumComputing/Matrix.lean` | Ported with redesign | Core aliases, adjoint, trace, projection, Kronecker product, normalized vectors, and unitarity are present using mathlib4 matrix APIs. |
| `src/matrix_inner_product.lean` | mathlib4 | Replaced | The old local inner-product-space development is not carried forward. Lean 4 proofs use matrix products and mathlib facts directly. |
| `src/matrix_lemmas.lean` | `QuantumComputing/Matrix.lean`, measurement modules | Partially ported | Public trace, projection, Kronecker, unitarity, and normalization facts are present. Cast-heavy tensor associativity, custom proof automation, and local normed-space instances remain intentionally unported. |
| `src/quantum.lean` | `QuantumComputing/States.lean`, `QuantumComputing/Gates/*`, `QuantumComputing/Measurement/*` | Ported with split modules | Named states, gates, projectors, measurement probabilities, and partial trace are split by topic. Old notations such as ket notation and measurement brackets are not restored. |
| `src/quantum_lemmas.lean` | `QuantumComputing/Gates/*`, `QuantumComputing/Measurement/*`, `QuantumComputing/Matrix.lean` | Partially ported | Gate facts, projector facts, trace facts, partial-trace facts, and state facts are present. The Lean 3 tactic layer is intentionally obsolete. |
| `src/measurement.lean` | `QuantumComputing/Measurement/Generalized.lean`, `QuantumComputing/Measurement/Projective.lean`, `QuantumComputing/Measurement/Computational.lean` | Mostly ported | Generalized/projective probabilities, post-measurement states, trace-form probability lemmas, post-measurement normalization, and projective-to-computational simulation facts are present in Lean 4 style. |
| `src/theorems/random-number-generator.lean` | `QuantumComputing/Theorems/RandomNumberGenerator.lean` | Ported and improved | Anonymous examples are now named theorems. |
| `src/theorems/no-cloning.lean` | `QuantumComputing/Theorems/NoCloning.lean` | Main results ported | `no_cloning_1`, `no_cloning_2`, and `no_cloning_3` are present. `no_cloning_3_alt` is intentionally skipped for now; see below. |
| Circuit layer | `QuantumComputing/Circuit*.lean` | New Lean 4 API | Typed circuit syntax and unitary circuit wrappers are new and have no Lean 3 counterpart. |

## Intentional Non-Ports

- The Lean 3 `meta def` tactic suite (`grind_matrix`, `finish_complex_arith`,
  `destruct_fin`, `solve_rng`, and related helpers) is not worth porting. Lean 4
  has better tactic support for the finite cases used here, and the old tactics
  were proof-engine scaffolding rather than quantum API.
- The old local inner-product, normed-group, normed-space, and metric-space
  instances for vectors are superseded by mathlib4. Reintroducing them locally
  would increase maintenance burden and overlap with library infrastructure.
- `no_cloning_3_alt` is not currently ported. Its Lean 3 proof is mainly a
  second proof route through partial measurement plus tensor-associativity casts.
  The Lean 4 `no_cloning_3` proof gives the same theorem with a smaller direct
  linearity argument and no cast-heavy infrastructure. Porting the alternative is
  only useful if we specifically want a partial-measurement demonstration theorem.

## Remaining Candidate Work

- Add focused aliases for renamed Lean 3 declarations only when downstream code
  needs source compatibility.
- Generalize finite gate proofs when a reusable theorem removes real duplication.
  For fixed 2-by-2 and 4-by-4 gates, the current `fin_cases` proofs are
  acceptable.
- If a user needs the partial-measurement no-cloning story, port a new theorem
  around the current `partialProb` API instead of translating the Lean 3 proof
  line by line.
