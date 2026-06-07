import QuantumComputing.Gates.Actions
import QuantumComputing.Gates.Projectors
import QuantumComputing.Gates.Properties

/-!
# Gate Decompositions

Identities expressing gates in terms of projectors, Hadamards, and controlled
operations.
-/

namespace QuantumComputing

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
  have h0 : ((I 2) ⊗ H) ⬝ (P0 ⊗ (I 2)) ⬝ ((I 2) ⊗ H) = P0 ⊗ (I 2) := by
    simpa [H_mul_self] using
      (Matrix.kron_mul_assoc (I 2) H P0 (I 2) (I 2) H)
  have h1 : ((I 2) ⊗ H) ⬝ (P1 ⊗ Z) ⬝ ((I 2) ⊗ H) = P1 ⊗ X := by
    simpa [H_Z_H_eq_X] using
      (Matrix.kron_mul_assoc (I 2) H P1 Z (I 2) H)
  calc
    P0 ⊗ (I 2) + P1 ⊗ X
        = ((I 2) ⊗ H) ⬝ (P0 ⊗ (I 2)) ⬝ ((I 2) ⊗ H) +
            ((I 2) ⊗ H) ⬝ (P1 ⊗ Z) ⬝ ((I 2) ⊗ H) := by
              rw [h0, h1]
    _ = ((I 2) ⊗ H) ⬝ (P0 ⊗ (I 2) + P1 ⊗ Z) ⬝ ((I 2) ⊗ H) := by
          simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem CZ_symmetry : CZ = SWAP ⬝ CZ ⬝ SWAP := by
  have h : gateControlled Z = SWAP ⬝ CZ ⬝ SWAP := by
    simp [gateControlled, controlledGate_Z]
  rw [gateControlled_Z] at h
  exact h

end QuantumComputing
