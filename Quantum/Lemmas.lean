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

@[simp]
theorem stateAfterMeasure_ket0_zero : stateAfterMeasure ket0 0 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stateAfterMeasure, measure, Matrix.proj, Matrix.mul, Matrix.adjoint, ket0,
      Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem stateAfterMeasure_ket1_one : stateAfterMeasure ket1 1 = ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [stateAfterMeasure, measure, Matrix.proj, Matrix.mul, Matrix.adjoint, ket1,
      Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem stateAfterMeasure_ketPlus_zero : stateAfterMeasure ketPlus 0 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateAfterMeasure, measure, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ket0,
      Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem stateAfterMeasure_ketPlus_one : stateAfterMeasure ketPlus 1 = ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateAfterMeasure, measure, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ket1,
      Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem stateAfterMeasure_ketMinus_zero : stateAfterMeasure ketMinus 0 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateAfterMeasure, measure, Matrix.proj, Matrix.mul, Matrix.adjoint, ketMinus, ket0,
      Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem stateAfterMeasure_ketMinus_one : stateAfterMeasure ketMinus 1 = -ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [stateAfterMeasure, measure, Matrix.proj, Matrix.mul, Matrix.adjoint, ketMinus, ket1,
      Vector.basis, _root_.Matrix.mul_apply]

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

@[simp]
theorem partialTrace_proj_ket00 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket00) = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTrace, Matrix.proj, Matrix.mul, Matrix.adjoint, ket00, P0, Vector.basis,
      _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]

@[simp]
theorem partialTrace_proj_ket01 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket01) = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTrace, Matrix.proj, Matrix.mul, Matrix.adjoint, ket01, P0, Vector.basis,
      _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]

@[simp]
theorem partialTrace_proj_ket10 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket10) = P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTrace, Matrix.proj, Matrix.mul, Matrix.adjoint, ket10, P1, Vector.basis,
      _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]

@[simp]
theorem partialTrace_proj_ket11 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket11) = P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTrace, Matrix.proj, Matrix.mul, Matrix.adjoint, ket11, P1, Vector.basis,
      _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat]

@[simp]
theorem partialTrace_proj_ketPhiPlus :
    partialTrace (n := 2) (m := 2) (Matrix.proj ketPhiPlus) = ((1 / 2 : ℂ) • (I 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTrace, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPhiPlus,
      _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_two]

end Quantum
