import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Quantum.Basic

namespace Quantum

namespace Vector

variable {n : ℕ}

@[simp]
theorem basis_apply (i j : Fin n) : basis i j 0 = if j = i then 1 else 0 :=
  rfl

theorem basis_apply_ne {i j : Fin n} (h : j ≠ i) : basis i j 0 = 0 := by
  simp [basis, h]

end Vector

@[simp]
theorem measure_basis_self {n : ℕ} (i : Fin n) : measure (Vector.basis i) i = 1 := by
  simp [measure]

theorem measure_basis_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) :
    measure (Vector.basis i) j = 0 := by
  simp [measure, Vector.basis_apply_ne h]

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

theorem X_isUnitary : Matrix.isUnitary X := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Matrix.adjoint, X, _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem Z_isUnitary : Matrix.isUnitary Z := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Matrix.adjoint, Z, _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem H_isUnitary : Matrix.isUnitary H := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Matrix.adjoint, H, _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem CNOT_isUnitary : Matrix.isUnitary CNOT := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Matrix.adjoint, CNOT, _root_.Matrix.mul_apply, Fin.sum_univ_four] <;>
    decide

theorem CZ_isUnitary : Matrix.isUnitary CZ := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Matrix.adjoint, CZ, _root_.Matrix.mul_apply, Fin.sum_univ_four] <;>
    decide

theorem SWAP_isUnitary : Matrix.isUnitary SWAP := by
  rw [Matrix.isUnitary_iff_adjoint_mul_self]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Matrix.adjoint, SWAP, _root_.Matrix.mul_apply, Fin.sum_univ_four] <;>
    decide

@[simp]
theorem X_mul_ket0 : X ⬝ ket0 = ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, X, ket0, ket1, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem X_mul_ket1 : X ⬝ ket1 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, X, ket0, ket1, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Z_mul_ket0 : Z ⬝ ket0 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Z, ket0, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Z_mul_ket1 : Z ⬝ ket1 = -ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Z, ket1, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem H_mul_ket0 : H ⬝ ket0 = ketPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, ket0, ketPlus, Vector.basis, _root_.Matrix.mul_apply,
      Fin.sum_univ_two]

@[simp]
theorem H_mul_ket1 : H ⬝ ket1 = ketMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, ket1, ketMinus, Vector.basis, _root_.Matrix.mul_apply,
      Fin.sum_univ_two]

end Quantum
