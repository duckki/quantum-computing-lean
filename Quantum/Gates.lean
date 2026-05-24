import Quantum.Projectors

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

@[simp]
theorem X_mul_ketPlus : X ⬝ ketPlus = ketPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, X, ketPlus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem X_mul_ketMinus : X ⬝ ketMinus = -ketMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, X, ketMinus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Z_mul_ketPlus : Z ⬝ ketPlus = ketMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Z, ketPlus, ketMinus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Z_mul_ketMinus : Z ⬝ ketMinus = ketPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Z, ketPlus, ketMinus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem H_mul_ketPlus : H ⬝ ketPlus = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, ketPlus, ket0, Vector.basis, _root_.Matrix.mul_apply,
      Fin.sum_univ_two]

@[simp]
theorem H_mul_ketMinus : H ⬝ ketMinus = ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, ketMinus, ket1, Vector.basis, _root_.Matrix.mul_apply,
      Fin.sum_univ_two]

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

@[simp]
theorem CNOT_mul_ket00 : CNOT ⬝ ket00 = ket00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, CNOT, ket00, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem CNOT_mul_ket01 : CNOT ⬝ ket01 = ket01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, CNOT, ket01, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem CNOT_mul_ket10 : CNOT ⬝ ket10 = ket11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, CNOT, ket10, ket11, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem CNOT_mul_ket11 : CNOT ⬝ ket11 = ket10 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, CNOT, ket10, ket11, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem CZ_mul_ket00 : CZ ⬝ ket00 = ket00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, CZ, ket00, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem CZ_mul_ket01 : CZ ⬝ ket01 = ket01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, CZ, ket01, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem CZ_mul_ket10 : CZ ⬝ ket10 = ket10 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, CZ, ket10, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem CZ_mul_ket11 : CZ ⬝ ket11 = -ket11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, CZ, ket11, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem SWAP_mul_ket00 : SWAP ⬝ ket00 = ket00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, SWAP, ket00, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem SWAP_mul_ket01 : SWAP ⬝ ket01 = ket10 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, SWAP, ket01, ket10, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem SWAP_mul_ket10 : SWAP ⬝ ket10 = ket01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, SWAP, ket01, ket10, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem SWAP_mul_ket11 : SWAP ⬝ ket11 = ket11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, SWAP, ket11, Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem controlledGate_X : controlledGate X = CNOT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controlledGate, Matrix.proj, Matrix.mul, Matrix.kron, X, CNOT, ket0, ket1,
      Vector.basis, _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]

@[simp]
theorem controlledGate_Z : controlledGate Z = CZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [controlledGate, Matrix.proj, Matrix.mul, Matrix.kron, Z, CZ, ket0, ket1,
      Vector.basis, _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]

@[simp]
theorem gateControlled_Z : gateControlled Z = CZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gateControlled, Matrix.mul, SWAP, CZ, controlledGate_Z, _root_.Matrix.mul_apply,
      Fin.sum_univ_four]

@[simp]
theorem gateControlled_X_mul_ket00 : gateControlled X ⬝ ket00 = ket00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gateControlled, Matrix.mul, SWAP, controlledGate_X, CNOT, ket00, Vector.basis,
      _root_.Matrix.mul_apply, Fin.sum_univ_four]

@[simp]
theorem gateControlled_X_mul_ket01 : gateControlled X ⬝ ket01 = ket11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gateControlled, Matrix.mul, SWAP, controlledGate_X, CNOT, ket01, ket11, Vector.basis,
      _root_.Matrix.mul_apply, Fin.sum_univ_four]

@[simp]
theorem gateControlled_X_mul_ket10 : gateControlled X ⬝ ket10 = ket10 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gateControlled, Matrix.mul, SWAP, controlledGate_X, CNOT, ket10, Vector.basis,
      _root_.Matrix.mul_apply, Fin.sum_univ_four]

@[simp]
theorem gateControlled_X_mul_ket11 : gateControlled X ⬝ ket11 = ket01 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gateControlled, Matrix.mul, SWAP, controlledGate_X, CNOT, ket01, ket11, Vector.basis,
      _root_.Matrix.mul_apply, Fin.sum_univ_four]

@[simp]
theorem H_kron_I_mul_ket00 : (H ⊗ (I 2)) ⬝ ket00 = ketPlus ⊗ ket0 := by
  rw [← ket0_kron_ket0, Matrix.kron_mul]
  rw [H_mul_ket0]
  simp [Matrix.mul]

@[simp]
theorem CNOT_mul_ketPlus_kron_ket0 : CNOT ⬝ (ketPlus ⊗ ket0) = ketPhiPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, Matrix.kron, CNOT, ketPlus, ket0, ketPhiPlus, Vector.basis,
      _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_four]

@[simp]
theorem bell_state_preparation : CNOT ⬝ ((H ⊗ (I 2)) ⬝ ket00) = ketPhiPlus := by
  rw [H_kron_I_mul_ket00, CNOT_mul_ketPlus_kron_ket0]

theorem SWAP_kron (a b : Vector 2) : SWAP ⬝ (a ⊗ b) = b ⊗ a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul, Matrix.kron, SWAP, _root_.Matrix.mul_apply, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Fin.sum_univ_four] <;>
    ring

theorem CNOT_decompose : CNOT = P0 ⊗ (I 2) + P1 ⊗ X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.kron, CNOT, P0, P1, X, finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem CZ_decompose : CZ = P0 ⊗ (I 2) + P1 ⊗ Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.kron, CZ, P0, P1, Z, finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem CZ_decompose_alt : CZ = (I 2) ⊗ P0 + Z ⊗ P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.kron, CZ, P0, P1, Z, finProdFinEquiv, Fin.divNat, Fin.modNat]

theorem H_P0_H_eq_PPlus : H ⬝ P0 ⬝ H = PPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, P0, PPlus, Matrix.proj, Matrix.adjoint, ketPlus,
      _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem H_P1_H_eq_PMinus : H ⬝ P1 ⬝ H = PMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, P1, PMinus, Matrix.proj, Matrix.adjoint, ketMinus,
      _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem H_Z_H_eq_X : H ⬝ Z ⬝ H = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, Z, X, _root_.Matrix.mul_apply, Fin.sum_univ_two]

theorem CNOT_eq_H_CZ_H : CNOT = ((I 2) ⊗ H) ⬝ CZ ⬝ ((I 2) ⊗ H) := by
  rw [CNOT_decompose, CZ_decompose]
  simp [H_Z_H_eq_X]

theorem CZ_symmetry : CZ = SWAP ⬝ CZ ⬝ SWAP := by
  have h : gateControlled Z = SWAP ⬝ CZ ⬝ SWAP := by
    simp [gateControlled, controlledGate_Z]
  rw [gateControlled_Z] at h
  exact h

end Quantum
