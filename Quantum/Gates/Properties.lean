import Quantum.Gates.Basic

/-!
# Gate Properties

Unitary, self-adjoint, and involutive facts for the named gates.
-/

namespace Quantum

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
theorem X_adjoint : X† = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, X]

@[simp]
theorem Z_adjoint : Z† = Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, Z]

@[simp]
theorem H_adjoint : H† = H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, H]

@[simp]
theorem CNOT_adjoint : CNOT† = CNOT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, CNOT]

@[simp]
theorem CZ_adjoint : CZ† = CZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, CZ]

@[simp]
theorem SWAP_adjoint : SWAP† = SWAP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, SWAP]

@[simp]
theorem X_mul_self : X ⬝ X = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, X, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Z_mul_self : Z ⬝ Z = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Z, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem H_mul_self : H ⬝ H = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem CNOT_mul_self : CNOT ⬝ CNOT = I 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, CNOT, _root_.Matrix.mul_apply, Fin.sum_univ_four] <;> decide

@[simp]
theorem CZ_mul_self : CZ ⬝ CZ = I 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, CZ, _root_.Matrix.mul_apply, Fin.sum_univ_four] <;> decide

@[simp]
theorem SWAP_mul_self : SWAP ⬝ SWAP = I 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, SWAP, _root_.Matrix.mul_apply, Fin.sum_univ_four] <;> decide

end Quantum
