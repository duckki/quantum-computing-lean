import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Kronecker
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

noncomputable def trace (A : Square n) : ℂ :=
  ∑ i, A i i

noncomputable def proj (s : Vector n) : Square n :=
  mul s (adjoint s)

noncomputable def kron {q : ℕ} (A : Matrix m n) (B : Matrix p q) : Matrix (m * p) (n * q) :=
  _root_.Matrix.reindex finProdFinEquiv finProdFinEquiv (_root_.Matrix.kronecker A B)

@[simp]
theorem adjoint_apply (A : Matrix m n) (i : Fin n) (j : Fin m) :
    adjoint A i j = star (A j i) :=
  rfl

@[simp]
theorem adjoint_adjoint (A : Matrix m n) : adjoint (adjoint A) = A := by
  simp [adjoint]

@[simp]
theorem adjoint_zero : adjoint (0 : Matrix m n) = 0 := by
  simp [adjoint]

@[simp]
theorem adjoint_one : adjoint (1 : Square n) = 1 := by
  simp [adjoint]

@[simp]
theorem adjoint_add (A B : Matrix m n) : adjoint (A + B) = adjoint A + adjoint B := by
  simp [adjoint]

@[simp]
theorem adjoint_mul (A : Matrix m n) (B : Matrix n p) :
    adjoint (mul A B) = mul (adjoint B) (adjoint A) := by
  simp [adjoint, mul]

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

def isUnit (s : Vector n) : Prop :=
  mul (adjoint s) s = 1

def isNormal (A : Square n) : Prop :=
  mul (adjoint A) A = mul A (adjoint A)

def isUnitary (A : Square n) : Prop :=
  mul (adjoint A) A = 1

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
