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

@[simp]
theorem normSq_invSqrt2 : Complex.normSq invSqrt2 = (1 / 2 : ℝ) := by
  rw [invSqrt2, Complex.normSq_ofReal]
  field_simp [
    ((Real.sqrt_ne_zero (x := 2) (by norm_num : (0 : ℝ) ≤ 2)).mpr
      (by norm_num : (2 : ℝ) ≠ 0))]
  rw [sq, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

@[simp]
theorem measure_ketPlus_zero : measure ketPlus 0 = (1 / 2 : ℝ) := by
  simp [measure, ketPlus]

@[simp]
theorem measure_ketPlus_one : measure ketPlus 1 = (1 / 2 : ℝ) := by
  simp [measure, ketPlus]

@[simp]
theorem measure_ketMinus_zero : measure ketMinus 0 = (1 / 2 : ℝ) := by
  simp [measure, ketMinus]

@[simp]
theorem measure_ketMinus_one : measure ketMinus 1 = (1 / 2 : ℝ) := by
  simp [measure, ketMinus, Complex.normSq_neg]

@[simp]
theorem measure_ketPhiPlus_zero : measure ketPhiPlus 0 = (1 / 2 : ℝ) := by
  simp [measure, ketPhiPlus]

@[simp]
theorem measure_ketPhiPlus_one : measure ketPhiPlus 1 = 0 := by
  simp [measure, ketPhiPlus]

@[simp]
theorem measure_ketPhiPlus_two : measure ketPhiPlus 2 = 0 := by
  simp [measure, ketPhiPlus]

@[simp]
theorem measure_ketPhiPlus_three : measure ketPhiPlus 3 = (1 / 2 : ℝ) := by
  simp [measure, ketPhiPlus]

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

end Quantum
