import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators

namespace Quantum

abbrev Matrix (m n : ℕ) := _root_.Matrix (Fin m) (Fin n) ℂ
abbrev Vector (n : ℕ) := Matrix n 1
abbrev Square (n : ℕ) := Matrix n n

namespace Matrix

variable {m n p : ℕ}

noncomputable abbrev adjoint (A : Matrix m n) : Matrix n m :=
  _root_.Matrix.conjTranspose A

noncomputable def mul (A : Matrix m n) (B : Matrix n p) : Matrix m p :=
  A * B

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
theorem adjoint_proj (s : Vector n) : adjoint (proj s) = proj s := by
  simp [proj]

@[simp]
theorem kron_apply {q : ℕ} (A : Matrix m n) (B : Matrix p q)
    (i : Fin m) (k : Fin p) (j : Fin n) (l : Fin q) :
    kron A B (finProdFinEquiv (i, k)) (finProdFinEquiv (j, l)) = A i j * B k l := by
  simp [kron]

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
theorem kron_one_one : kron (1 : Square m) (1 : Square n) = (1 : Square (m * n)) := by
  ext i j
  rw [← finProdFinEquiv.apply_symm_apply i, ← finProdFinEquiv.apply_symm_apply j]
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [kron, _root_.Matrix.one_apply, Prod.ext_iff]

def isUnit (s : Vector n) : Prop :=
  mul (adjoint s) s = 1

theorem proj_mul_proj_of_isUnit {s : Vector n} (hs : isUnit s) :
    mul (proj s) (proj s) = proj s := by
  change (s * adjoint s) * (s * adjoint s) = s * adjoint s
  rw [_root_.Matrix.mul_assoc]
  rw [← _root_.Matrix.mul_assoc (adjoint s) s (adjoint s)]
  have hsroot : adjoint s * s = 1 := by simpa [isUnit, mul] using hs
  rw [hsroot]
  simp

theorem trace_proj_of_isUnit {s : Vector n} (hs : isUnit s) : trace (proj s) = 1 := by
  rw [proj]
  rw [trace_mul_comm]
  rw [isUnit] at hs
  rw [hs]
  simp [trace]

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

theorem isUnitary_mul_isUnit {A : Square n} {s : Vector n}
    (hA : isUnitary A) (hs : isUnit s) : isUnit (mul A s) := by
  rw [isUnit] at hs ⊢
  rw [adjoint_mul]
  rw [isUnitary_iff_adjoint_mul_self] at hA
  have hAroot : adjoint A * A = 1 := by simpa [mul] using hA
  have hsroot : adjoint s * s = 1 := by simpa [mul] using hs
  change (adjoint s * adjoint A) * (A * s) = 1
  rw [_root_.Matrix.mul_assoc]
  rw [← _root_.Matrix.mul_assoc (adjoint A) A s]
  rw [hAroot]
  simpa using hsroot

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

def basis (i : Fin n) : Vector n :=
  fun j _ => if j = i then 1 else 0

end Vector

end Quantum
