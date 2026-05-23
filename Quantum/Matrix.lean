import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Mul

open scoped BigOperators

namespace Quantum

abbrev Matrix (m n : ℕ) := _root_.Matrix (Fin m) (Fin n) ℂ
abbrev Vector (n : ℕ) := Matrix n 1
abbrev Square (n : ℕ) := Matrix n n

namespace Matrix

variable {m n p : ℕ}

noncomputable def adjoint (A : Matrix m n) : Matrix n m :=
  fun i j => star (A j i)

noncomputable def mul (A : Matrix m n) (B : Matrix n p) : Matrix m p :=
  A * B

noncomputable def trace (A : Square n) : ℂ :=
  ∑ i, A i i

noncomputable def proj (s : Vector n) : Square n :=
  mul s (adjoint s)

def isUnit (s : Vector n) : Prop :=
  mul (adjoint s) s = 1

def isNormal (A : Square n) : Prop :=
  mul (adjoint A) A = mul A (adjoint A)

def isUnitary (A : Square n) : Prop :=
  mul (adjoint A) A = 1

end Matrix

postfix:max "†" => Matrix.adjoint
infixl:70 " ⬝ " => Matrix.mul
notation "Tr(" A ")" => Matrix.trace A
notation "I" n => (1 : Square n)

namespace Vector

variable {n : ℕ}

def basis (i : Fin n) : Vector n :=
  fun j _ => if j = i then 1 else 0

end Vector

end Quantum
