import Quantum.Core

namespace Quantum

theorem ket0_isUnit : Matrix.isUnit ket0 := by
  rw [Matrix.isUnit]
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ket0, Vector.basis, _root_.Matrix.mul_apply,
    Fin.sum_univ_two]

theorem ket1_isUnit : Matrix.isUnit ket1 := by
  rw [Matrix.isUnit]
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ket1, Vector.basis, _root_.Matrix.mul_apply,
    Fin.sum_univ_two]

theorem ketPlus_isUnit : Matrix.isUnit ketPlus := by
  rw [Matrix.isUnit]
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ketPlus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem ketMinus_isUnit : Matrix.isUnit ketMinus := by
  rw [Matrix.isUnit]
  ext i j
  fin_cases i; fin_cases j
  norm_num [Matrix.mul, Matrix.adjoint, ketMinus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem ketPhiPlus_isUnit : Matrix.isUnit ketPhiPlus := by
  rw [Matrix.isUnit]
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul, Matrix.adjoint, ketPhiPlus, _root_.Matrix.mul_apply, Fin.sum_univ_four]
  norm_num

@[simp]
theorem proj_ket0 : Matrix.proj ket0 = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.proj, Matrix.mul, Matrix.adjoint, P0, ket0, Vector.basis,
      _root_.Matrix.mul_apply, Fin.sum_univ_one]

@[simp]
theorem proj_ket1 : Matrix.proj ket1 = P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.proj, Matrix.mul, Matrix.adjoint, P1, ket1, Vector.basis,
      _root_.Matrix.mul_apply, Fin.sum_univ_one]

end Quantum
