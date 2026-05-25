import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Complex Matrices

Finite-dimensional complex matrices, state vectors, adjoints, traces,
Kronecker products, projections, and normalized-vector predicates.
-/

open scoped BigOperators

namespace QuantumComputing

abbrev Matrix (m n : ℕ) := _root_.Matrix (Fin m) (Fin n) ℂ
abbrev Vector (n : ℕ) := Matrix n 1
abbrev Square (n : ℕ) := Matrix n n

namespace Matrix

variable {m n p : ℕ}

noncomputable abbrev adjoint (A : Matrix m n) : Matrix n m :=
  _root_.Matrix.conjTranspose A

noncomputable def mul (A : Matrix m n) (B : Matrix n p) : Matrix m p :=
  A * B

@[simp]
theorem mul_add (A : Matrix m n) (B C : Matrix n p) :
    mul A (B + C) = mul A B + mul A C := by
  simp [mul, _root_.Matrix.mul_add]

@[simp]
theorem add_mul (A B : Matrix m n) (C : Matrix n p) :
    mul (A + B) C = mul A C + mul B C := by
  simp [mul, _root_.Matrix.add_mul]

@[simp]
theorem mul_zero (A : Matrix m n) : mul A (0 : Matrix n p) = 0 := by
  simp [mul]

@[simp]
theorem zero_mul (A : Matrix n p) : mul (0 : Matrix m n) A = 0 := by
  simp [mul]

@[simp]
theorem mul_one (A : Matrix m n) : mul A (1 : Square n) = A := by
  simp [mul]

@[simp]
theorem one_mul (A : Matrix m n) : mul (1 : Square m) A = A := by
  simp [mul]

@[simp]
theorem mul_smul (A : Matrix m n) (a : ℂ) (B : Matrix n p) :
    mul A (a • B) = a • mul A B := by
  simp [mul]

@[simp]
theorem smul_mul (a : ℂ) (A : Matrix m n) (B : Matrix n p) :
    mul (a • A) B = a • mul A B := by
  simp [mul]

noncomputable abbrev trace (A : Square n) : ℂ :=
  _root_.Matrix.trace A

noncomputable def proj (s : Vector n) : Square n :=
  mul s (adjoint s)

noncomputable def kron {q : ℕ} (A : Matrix m n) (B : Matrix p q) : Matrix (m * p) (n * q) :=
  _root_.Matrix.reindex finProdFinEquiv finProdFinEquiv (_root_.Matrix.kronecker A B)

@[simp]
theorem adjoint_mul (A : Matrix m n) (B : Matrix n p) :
    adjoint (mul A B) = mul (adjoint B) (adjoint A) := by
  simp [adjoint, mul]

theorem trace_mul_comm (A : Matrix m n) (B : Matrix n m) :
    trace (mul A B) = trace (mul B A) := by
  simpa [trace, mul] using _root_.Matrix.trace_mul_comm A B

@[simp]
theorem adjoint_zero : adjoint (0 : Matrix m n) = 0 := by
  simp [adjoint]

@[simp]
theorem adjoint_one : adjoint (1 : Square n) = 1 := by
  simp [adjoint]

@[simp]
theorem adjoint_adjoint (A : Matrix m n) : adjoint (adjoint A) = A := by
  ext i j
  simp [adjoint]

theorem adjoint_inj {A B : Matrix m n} (h : adjoint A = adjoint B) : A = B := by
  rw [← adjoint_adjoint A, h, adjoint_adjoint]

@[simp]
theorem adjoint_add (A B : Matrix m n) : adjoint (A + B) = adjoint A + adjoint B := by
  simp [adjoint]

@[simp]
theorem adjoint_neg (A : Matrix m n) : adjoint (-A) = -adjoint A := by
  simp [adjoint]

@[simp]
theorem adjoint_sub (A B : Matrix m n) : adjoint (A - B) = adjoint A - adjoint B := by
  simp [sub_eq_add_neg]

@[simp]
theorem adjoint_smul (a : ℂ) (A : Matrix m n) : adjoint (a • A) = star a • adjoint A := by
  simp [adjoint]

@[simp]
theorem adjoint_apply (A : Matrix m n) (i : Fin n) (j : Fin m) :
    adjoint A i j = star (A j i) :=
  rfl

theorem trace_smul (a : ℂ) (A : Square n) : trace (a • A) = a * trace A := by
  simp [trace, _root_.Matrix.trace, Finset.mul_sum]

@[simp]
theorem trace_zero : trace (0 : Square n) = 0 := by
  simp [trace]

theorem trace_adjoint (A : Square n) : trace (adjoint A) = star (trace A) := by
  simp [trace, adjoint, _root_.Matrix.trace]

@[simp]
theorem adjoint_proj (s : Vector n) : adjoint (proj s) = proj s := by
  simp [proj]

theorem proj_add (s t : Vector n) :
    proj (s + t) =
      proj s + mul s (adjoint t) + mul t (adjoint s) + proj t := by
  ext i j
  simp [proj, mul, adjoint, _root_.Matrix.mul_apply]
  ring

@[simp]
theorem kron_apply {q : ℕ} (A : Matrix m n) (B : Matrix p q)
    (i : Fin m) (k : Fin p) (j : Fin n) (l : Fin q) :
    kron A B (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) = A i j * B k l := by
  simp [kron]

@[simp]
theorem kron_zero_left {q : ℕ} (B : Matrix p q) :
    kron (0 : Matrix m n) B = 0 := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron]

@[simp]
theorem kron_zero_right {q : ℕ} (A : Matrix m n) :
    kron A (0 : Matrix p q) = 0 := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron]

theorem kron_add_left {q : ℕ} (A B : Matrix m n) (C : Matrix p q) :
    kron (A + B) C = kron A C + kron B C := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron, _root_.add_mul]

theorem kron_add_right {q : ℕ} (A : Matrix m n) (B C : Matrix p q) :
    kron A (B + C) = kron A B + kron A C := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron, _root_.mul_add]

theorem kron_sub_left {q : ℕ} (A B : Matrix m n) (C : Matrix p q) :
    kron (A - B) C = kron A C - kron B C := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron, sub_eq_add_neg, _root_.add_mul]

theorem kron_sub_right {q : ℕ} (A : Matrix m n) (B C : Matrix p q) :
    kron A (B - C) = kron A B - kron A C := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron, sub_eq_add_neg, _root_.mul_add]

theorem kron_smul_left {q : ℕ} (a : ℂ) (A : Matrix m n) (B : Matrix p q) :
    kron (a • A) B = a • kron A B := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron, mul_assoc]

theorem kron_smul_right {q : ℕ} (a : ℂ) (A : Matrix m n) (B : Matrix p q) :
    kron A (a • B) = a • kron A B := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron, mul_left_comm]

@[simp]
theorem adjoint_kron {q : ℕ} (A : Matrix m n) (B : Matrix p q) :
    adjoint (kron A B) = kron (adjoint A) (adjoint B) := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [adjoint, kron, _root_.Matrix.kronecker]

@[simp]
theorem kron_mul {q r s : ℕ} (A : Matrix m n) (B : Matrix p q)
    (C : Matrix n r) (D : Matrix q s) :
    mul (kron A B) (kron C D) = kron (mul A C) (mul B D) := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [mul, kron, _root_.Matrix.mul_kronecker_mul]

@[simp]
theorem proj_kron (s : Vector m) (t : Vector n) :
    proj (kron s t) = kron (proj s) (proj t) := by
  rw [proj, adjoint_kron, kron_mul]
  rfl

theorem proj_add_kron (s t : Vector m) (u v : Vector n) :
    proj (kron s u + kron t v) =
      kron (proj s) (proj u) + kron (mul s (adjoint t)) (mul u (adjoint v)) +
        kron (mul t (adjoint s)) (mul v (adjoint u)) + kron (proj t) (proj v) := by
  rw [proj_add, proj_kron, proj_kron]
  rw [adjoint_kron, adjoint_kron, kron_mul, kron_mul]

@[simp]
theorem kron_one_one : kron (1 : Square m) (1 : Square n) = (1 : Square (m * n)) := by
  ext i j
  rw [← finProdFinEquiv.apply_symm_apply i, ← finProdFinEquiv.apply_symm_apply j]
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron, _root_.Matrix.one_apply, Prod.ext_iff]

theorem trace_kron (A : Square m) (B : Square n) :
    trace (kron A B) = trace A * trace B := by
  calc
    trace (kron A B) = ∑ x : Fin m × Fin n, A x.1 x.1 * B x.2 x.2 := by
      rw [trace, _root_.Matrix.trace]
      symm
      exact Fintype.sum_equiv finProdFinEquiv
        (fun x : Fin m × Fin n => A x.1 x.1 * B x.2 x.2)
        (fun x : Fin (m * n) => kron A B x x)
        (by intro x; simp [kron])
    _ = trace A * trace B := by
      rw [trace, trace, _root_.Matrix.trace, _root_.Matrix.trace]
      rw [← Finset.univ_product_univ]
      rw [Finset.sum_product]
      rw [Finset.sum_comm]
      simp [Finset.mul_sum, mul_comm]

theorem trace_outer_eq_inner (s t : Vector n) :
    trace (mul s (adjoint t)) = (mul (adjoint t) s) 0 0 := by
  rw [trace_mul_comm]
  simp [trace, mul, _root_.Matrix.trace]

theorem trace_proj (s : Vector n) : trace (proj s) = (mul (adjoint s) s) 0 0 := by
  simp [proj, trace_outer_eq_inner]

def isNormal (A : Square n) : Prop :=
  mul (adjoint A) A = mul A (adjoint A)

def isUnitary (A : Square n) : Prop :=
  A ∈ _root_.Matrix.unitaryGroup (Fin n) ℂ

theorem isUnitary_iff_adjoint_mul_self (A : Square n) :
    isUnitary A ↔ mul (adjoint A) A = 1 := by
  simpa [isUnitary, adjoint, mul, _root_.Matrix.star_eq_conjTranspose] using
    (_root_.Matrix.mem_unitaryGroup_iff' (A := A))

theorem isUnitary_iff_mul_adjoint_self (A : Square n) :
    isUnitary A ↔ mul A (adjoint A) = 1 := by
  simpa [isUnitary, adjoint, mul, _root_.Matrix.star_eq_conjTranspose] using
    (_root_.Matrix.mem_unitaryGroup_iff (A := A))

@[simp]
theorem isUnitary_one : isUnitary (1 : Square n) := by
  rw [isUnitary_iff_adjoint_mul_self]
  simp [mul]

theorem isUnitary_mul {A B : Square n}
    (hA : isUnitary A) (hB : isUnitary B) : isUnitary (mul A B) := by
  rw [isUnitary_iff_adjoint_mul_self]
  rw [adjoint_mul]
  rw [isUnitary_iff_adjoint_mul_self] at hA hB
  have hAroot : adjoint A * A = 1 := by simpa [mul] using hA
  have hBroot : adjoint B * B = 1 := by simpa [mul] using hB
  change (adjoint B * adjoint A) * (A * B) = 1
  rw [_root_.Matrix.mul_assoc]
  rw [← _root_.Matrix.mul_assoc (adjoint A) A B]
  rw [hAroot]
  simp [hBroot]

theorem isUnitary_preserve_inner {U : Square n} (hU : isUnitary U) (v w : Vector n) :
    mul (adjoint (mul U v)) (mul U w) = mul (adjoint v) w := by
  rw [adjoint_mul]
  rw [isUnitary_iff_adjoint_mul_self] at hU
  have hUroot : adjoint U * U = 1 := by simpa [mul] using hU
  change (adjoint v * adjoint U) * (U * w) = adjoint v * w
  rw [_root_.Matrix.mul_assoc]
  rw [← _root_.Matrix.mul_assoc (adjoint U) U w]
  rw [hUroot]
  simp

theorem isUnitary_kron {A : Square m} {B : Square n}
    (hA : isUnitary A) (hB : isUnitary B) : isUnitary (kron A B) := by
  rw [isUnitary_iff_adjoint_mul_self]
  rw [adjoint_kron, kron_mul]
  rw [isUnitary_iff_adjoint_mul_self] at hA hB
  simp [hA, hB]

end Matrix

postfix:max "†" => Matrix.adjoint
infixl:70 " ⬝ " => Matrix.mul
infixl:75 " ⊗ " => Matrix.kron
notation "Tr(" A ")" => Matrix.trace A
notation "I" n => (1 : Square n)

namespace Vector

variable {n : ℕ}

/-- A state vector is normalized when its inner product with itself is `1`. -/
def IsNormalized (s : Vector n) : Prop :=
  s† ⬝ s = 1

theorem isNormalized_kron {m n : ℕ} {s : Vector m} {t : Vector n}
    (hs : IsNormalized s) (ht : IsNormalized t) : IsNormalized (s ⊗ t) := by
  rw [IsNormalized, Matrix.adjoint_kron, Matrix.kron_mul]
  have hsroot : s† ⬝ s = (1 : Square 1) := by simpa [IsNormalized] using hs
  have htroot : t† ⬝ t = (1 : Square 1) := by simpa [IsNormalized] using ht
  rw [hsroot, htroot]
  simp

theorem not_isNormalized_zero (n : ℕ) : ¬ IsNormalized (0 : Vector n) := by
  intro h
  have hscalar := congrFun (congrFun h 0) 0
  norm_num [IsNormalized, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply] at hscalar

def basis (i : Fin n) : Vector n :=
  fun j _ => if j = i then 1 else 0

@[simp]
theorem basis_apply (i j : Fin n) : basis i j 0 = if j = i then 1 else 0 :=
  rfl

theorem basis_apply_ne {i j : Fin n} (h : j ≠ i) : basis i j 0 = 0 := by
  simp [basis, h]

theorem basis_isNormalized (i : Fin n) : IsNormalized (basis i) := by
  rw [IsNormalized]
  ext j k
  fin_cases j
  fin_cases k
  simp [Matrix.mul, Matrix.adjoint, basis, _root_.Matrix.mul_apply]

end Vector

namespace Matrix

variable {m n p : ℕ}

theorem proj_mul_proj_of_isNormalized {s : Vector n} (hs : Vector.IsNormalized s) :
    mul (proj s) (proj s) = proj s := by
  change (s * adjoint s) * (s * adjoint s) = s * adjoint s
  rw [_root_.Matrix.mul_assoc]
  rw [← _root_.Matrix.mul_assoc (adjoint s) s (adjoint s)]
  have hsroot : adjoint s * s = 1 := by simpa [Vector.IsNormalized, mul] using hs
  rw [hsroot]
  simp

theorem trace_proj_of_isNormalized {s : Vector n} (hs : Vector.IsNormalized s) :
    trace (proj s) = 1 := by
  rw [proj]
  rw [trace_mul_comm]
  rw [Vector.IsNormalized] at hs
  rw [hs]
  simp [trace]

theorem isUnitary_mul_isNormalized {A : Square n} {s : Vector n}
    (hA : isUnitary A) (hs : Vector.IsNormalized s) :
    Vector.IsNormalized (mul A s) := by
  rw [Vector.IsNormalized] at hs ⊢
  rw [adjoint_mul]
  rw [isUnitary_iff_adjoint_mul_self] at hA
  have hAroot : adjoint A * A = 1 := by simpa [mul] using hA
  have hsroot : adjoint s * s = 1 := by simpa [mul] using hs
  change (adjoint s * adjoint A) * (A * s) = 1
  rw [_root_.Matrix.mul_assoc]
  rw [← _root_.Matrix.mul_assoc (adjoint A) A s]
  rw [hAroot]
  simpa using hsroot

end Matrix

end QuantumComputing
