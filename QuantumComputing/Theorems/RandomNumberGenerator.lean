import QuantumComputing.Measurement.Computational
import QuantumComputing.Notation

/-!
# Random Number Generator Theorems

Uniform measurement probabilities for Hadamard-based random-number generator
states.
-/

namespace QuantumComputing

open scoped QuantumComputing

namespace Theorems.RandomNumberGenerator

open Measurement

/-- Two-qubit Hadamard gate used by the random-number-generator examples. -/
noncomputable def H2 : Square 4 :=
  H ⊗ H

theorem H_ket0_uniform (i : Fin 2) : prob (H ⬝ |0⟩) i = (1 / 2 : ℝ) := by
  fin_cases i <;> simp

theorem H_ket1_uniform (i : Fin 2) : prob (H ⬝ |1⟩) i = (1 / 2 : ℝ) := by
  fin_cases i <;> simp

@[simp]
theorem H2_mul_ket00 : H2 ⬝ |00⟩ = |+⟩ ⊗ |+⟩ := by
  rw [H2, ← ket0_kron_ket0, Matrix.kron_mul]
  change (H ⬝ |0⟩) ⊗ (H ⬝ |0⟩) = |+⟩ ⊗ |+⟩
  simp

@[simp]
theorem H2_mul_ket01 : H2 ⬝ |01⟩ = |+⟩ ⊗ |-⟩ := by
  rw [H2, ← ket0_kron_ket1, Matrix.kron_mul]
  change (H ⬝ |0⟩) ⊗ (H ⬝ |1⟩) = |+⟩ ⊗ |-⟩
  simp

@[simp]
theorem H2_mul_ket10 : H2 ⬝ |10⟩ = |-⟩ ⊗ |+⟩ := by
  rw [H2, ← ket1_kron_ket0, Matrix.kron_mul]
  change (H ⬝ |1⟩) ⊗ (H ⬝ |0⟩) = |-⟩ ⊗ |+⟩
  simp

@[simp]
theorem H2_mul_ket11 : H2 ⬝ |11⟩ = |-⟩ ⊗ |-⟩ := by
  rw [H2, ← ket1_kron_ket1, Matrix.kron_mul]
  change (H ⬝ |1⟩) ⊗ (H ⬝ |1⟩) = |-⟩ ⊗ |-⟩
  simp

theorem H2_ket00_uniform (i : Fin 4) : prob (H2 ⬝ |00⟩) i = (1 / 4 : ℝ) := by
  fin_cases i <;>
    simp [prob, Matrix.kron, ketPlus, finProdFinEquiv, Fin.divNat, Fin.modNat] <;>
    norm_num

theorem H2_ket01_uniform (i : Fin 4) : prob (H2 ⬝ |01⟩) i = (1 / 4 : ℝ) := by
  fin_cases i <;>
    simp [prob, Matrix.kron, ketPlus, ketMinus, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.normSq_neg] <;>
    norm_num

theorem H2_ket10_uniform (i : Fin 4) : prob (H2 ⬝ |10⟩) i = (1 / 4 : ℝ) := by
  fin_cases i <;>
    simp [prob, Matrix.kron, ketPlus, ketMinus, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.normSq_neg] <;>
    norm_num

theorem H2_ket11_uniform (i : Fin 4) : prob (H2 ⬝ |11⟩) i = (1 / 4 : ℝ) := by
  fin_cases i <;>
    simp [prob, Matrix.kron, ketMinus, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.normSq_neg] <;>
    norm_num

end Theorems.RandomNumberGenerator

end QuantumComputing
