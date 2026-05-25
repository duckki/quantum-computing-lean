import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import QuantumComputing.Matrix

/-!
# Named State Vectors

Common computational-basis, Hadamard-basis, and Bell state vectors, together
with their normalization facts.
-/

namespace QuantumComputing

noncomputable def invSqrt2 : ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ)

def ket0 : Vector 2 := Vector.basis 0
def ket1 : Vector 2 := Vector.basis 1

def ket00 : Vector 4 := Vector.basis 0
def ket01 : Vector 4 := Vector.basis 1
def ket10 : Vector 4 := Vector.basis 2
def ket11 : Vector 4 := Vector.basis 3

def ketZeros (n : ℕ) : Vector (2 ^ n) :=
  Vector.basis ⟨0, by simp⟩

noncomputable def ketPlus : Vector 2 :=
  fun i _ => if (i : ℕ) = 0 then invSqrt2 else invSqrt2

noncomputable def ketMinus : Vector 2 :=
  fun i _ => if (i : ℕ) = 0 then invSqrt2 else -invSqrt2

noncomputable def ketPhiPlus : Vector 4 :=
  fun i _ =>
    if (i : ℕ) = 0 then invSqrt2
    else if (i : ℕ) = 3 then invSqrt2
    else 0

@[simp]
theorem star_invSqrt2 : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2]

@[simp]
theorem invSqrt2_mul_self : invSqrt2 * invSqrt2 = (1 / 2 : ℂ) := by
  rw [invSqrt2]
  simp
  field_simp [
    Complex.ofReal_ne_zero.mpr
      ((Real.sqrt_ne_zero (x := 2) (by norm_num : (0 : ℝ) ≤ 2)).mpr
        (by norm_num : (2 : ℝ) ≠ 0))]
  rw [sq, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

@[simp]
theorem sqrt_two_mul_invSqrt2 : ((Real.sqrt 2 : ℝ) : ℂ) * invSqrt2 = 1 := by
  rw [invSqrt2]
  rw [← Complex.ofReal_mul]
  congr
  field_simp [
    ((Real.sqrt_ne_zero (x := 2) (by norm_num : (0 : ℝ) ≤ 2)).mpr
      (by norm_num : (2 : ℝ) ≠ 0))]

@[simp]
theorem normSq_invSqrt2 : Complex.normSq invSqrt2 = (1 / 2 : ℝ) := by
  rw [invSqrt2, Complex.normSq_ofReal]
  field_simp [
    ((Real.sqrt_ne_zero (x := 2) (by norm_num : (0 : ℝ) ≤ 2)).mpr
      (by norm_num : (2 : ℝ) ≠ 0))]
  rw [sq, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem ket0_isNormalized : Vector.IsNormalized ket0 := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ket0, Vector.basis, _root_.Matrix.mul_apply,
    Fin.sum_univ_two]

theorem ket1_isNormalized : Vector.IsNormalized ket1 := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ket1, Vector.basis, _root_.Matrix.mul_apply,
    Fin.sum_univ_two]

theorem ketPlus_isNormalized : Vector.IsNormalized ketPlus := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ketPlus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem ketMinus_isNormalized : Vector.IsNormalized ketMinus := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ketMinus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem ketPhiPlus_isNormalized : Vector.IsNormalized ketPhiPlus := by
  rw [Vector.IsNormalized]
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul, Matrix.adjoint, ketPhiPlus, _root_.Matrix.mul_apply, Fin.sum_univ_four]
  norm_num

@[simp]
theorem ket0_kron_ket0 : ket0 ⊗ ket0 = ket00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.kron, ket0, ket00, Vector.basis, finProdFinEquiv, Fin.divNat, Fin.modNat]

@[simp]
theorem ket0_kron_ket1 : ket0 ⊗ ket1 = ket01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.kron, ket0, ket1, ket01, Vector.basis, finProdFinEquiv, Fin.divNat,
      Fin.modNat]

@[simp]
theorem ket1_kron_ket0 : ket1 ⊗ ket0 = ket10 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.kron, ket0, ket1, ket10, Vector.basis, finProdFinEquiv, Fin.divNat,
      Fin.modNat]

@[simp]
theorem ket1_kron_ket1 : ket1 ⊗ ket1 = ket11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.kron, ket1, ket11, Vector.basis, finProdFinEquiv, Fin.divNat, Fin.modNat]

end QuantumComputing
