import Mathlib.LinearAlgebra.Matrix.Reindex
import Quantum.State
import Quantum.States

/-!
# Qubit Registers

Aliases and tensoring operations for `n`-qubit registers with dimension
`2 ^ n`.
-/

namespace Quantum

namespace Circuit

namespace Register

/-- The Hilbert-space dimension of an `n`-qubit register. -/
def dimension (n : ℕ) : ℕ :=
  2 ^ n

/-- State vectors for an `n`-qubit register. -/
abbrev State (n : ℕ) := Vector (dimension n)

/-- Gates on an `n`-qubit register. -/
abbrev Gate (n : ℕ) := Square (dimension n)

/-- Density matrices on an `n`-qubit register. -/
abbrev Density (n : ℕ) := DensityMatrix (dimension n)

/-- Pure states on an `n`-qubit register. -/
abbrev Pure (n : ℕ) := PureState (dimension n)

/-- Computational basis vector for an `n`-qubit register. -/
def basis {n : ℕ} (i : Fin (dimension n)) : State n :=
  Vector.basis i

/-- The all-zero computational basis state for an `n`-qubit register. -/
def zeros (n : ℕ) : State n :=
  ketZeros n

/-- Reindex a vector along an equivalence of finite dimensions. -/
noncomputable def reindexVector {n m : ℕ} (e : Fin n ≃ Fin m) (s : Vector n) : Vector m :=
  _root_.Matrix.reindex e (Equiv.refl (Fin 1)) s

/-- Reindex a square matrix along an equivalence of finite dimensions. -/
noncomputable def reindexSquare {n m : ℕ} (e : Fin n ≃ Fin m) (A : Square n) : Square m :=
  _root_.Matrix.reindex e e A

/-- The dimension equivalence identifying tensor products of qubit registers. -/
noncomputable def tensorEquiv (n m : ℕ) :
    Fin (dimension n * dimension m) ≃ Fin (dimension (n + m)) :=
  finCongr (by simp [dimension, Nat.pow_add])

/-- Tensor two register state vectors and reindex the result to `2 ^ (n + m)`. -/
noncomputable def tensorState {n m : ℕ} (s : State n) (t : State m) : State (n + m) :=
  reindexVector (tensorEquiv n m) (s ⊗ t)

/-- Tensor two register gates and reindex the result to `2 ^ (n + m)`. -/
noncomputable def tensorGate {n m : ℕ} (U : Gate n) (V : Gate m) : Gate (n + m) :=
  reindexSquare (tensorEquiv n m) (U ⊗ V)

/-- Tensor two register density matrices and reindex the result to `2 ^ (n + m)`. -/
noncomputable def tensorDensity {n m : ℕ} (ρ : Density n) (σ : Density m) : Density (n + m) :=
  reindexSquare (tensorEquiv n m) (ρ ⊗ σ)

@[simp]
theorem reindexVector_apply {n m : ℕ} (e : Fin n ≃ Fin m) (s : Vector n) (i : Fin m) :
    reindexVector e s i 0 = s (e.symm i) 0 := by
  simp [reindexVector]

@[simp]
theorem reindexSquare_apply {n m : ℕ} (e : Fin n ≃ Fin m) (A : Square n) (i j : Fin m) :
    reindexSquare e A i j = A (e.symm i) (e.symm j) := by
  simp [reindexSquare]

@[simp]
theorem tensorState_apply {n m : ℕ} (s : State n) (t : State m)
    (i : Fin (dimension (n + m))) :
    tensorState s t i 0 = (s ⊗ t) ((tensorEquiv n m).symm i) 0 := by
  simp [tensorState]

@[simp]
theorem tensorGate_apply {n m : ℕ} (U : Gate n) (V : Gate m)
    (i j : Fin (dimension (n + m))) :
    tensorGate U V i j = (U ⊗ V) ((tensorEquiv n m).symm i) ((tensorEquiv n m).symm j) := by
  simp [tensorGate]

@[simp]
theorem adjoint_reindexSquare {n m : ℕ} (e : Fin n ≃ Fin m) (A : Square n) :
    (reindexSquare e A)† = reindexSquare e (A†) := by
  simp [reindexSquare, Matrix.adjoint]

@[simp]
theorem reindexSquare_mul {n m : ℕ} (e : Fin n ≃ Fin m) (A B : Square n) :
    reindexSquare e (A ⬝ B) = reindexSquare e A ⬝ reindexSquare e B := by
  simp [reindexSquare, Matrix.mul]

@[simp]
theorem reindexSquare_one {n m : ℕ} (e : Fin n ≃ Fin m) :
    reindexSquare e (I n) = I m := by
  ext i j
  by_cases h : i = j
  · subst j
    simp [reindexSquare]
  · have hsym : e.symm i ≠ e.symm j := fun hs => h (e.symm.injective hs)
    simp [reindexSquare, h, hsym]

theorem isUnitary_reindexSquare {n m : ℕ} (e : Fin n ≃ Fin m) {U : Square n}
    (hU : Matrix.isUnitary U) :
    Matrix.isUnitary (reindexSquare e U) := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  rw [adjoint_reindexSquare, ← reindexSquare_mul]
  rw [Matrix.isUnitary_iff_adjoint_mul_self] at hU
  rw [hU]
  simp

theorem isUnitary_tensorGate {n m : ℕ} {U : Gate n} {V : Gate m}
    (hU : Matrix.isUnitary U) (hV : Matrix.isUnitary V) :
    Matrix.isUnitary (tensorGate U V) := by
  exact isUnitary_reindexSquare (tensorEquiv n m) (Matrix.isUnitary_kron hU hV)

end Register

end Circuit

end Quantum
