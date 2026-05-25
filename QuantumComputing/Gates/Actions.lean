import QuantumComputing.Gates.Basic

/-!
# Gate Actions

Action of the named gates and controlled gates on named state vectors.
-/

namespace QuantumComputing

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

end QuantumComputing
