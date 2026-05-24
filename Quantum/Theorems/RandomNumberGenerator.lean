import Quantum.Gates
import Quantum.Measurement.Lemmas

namespace Quantum

namespace Theorems.RandomNumberGenerator

open Measurement

/-- Two-qubit Hadamard gate used by the random-number-generator examples. -/
noncomputable def H2 : Square 4 :=
  H ⊗ H

theorem H_ket0_uniform (i : Fin 2) :
    prob (H ⬝ ket0) i = (1 / 2 : ℝ) := by
  fin_cases i <;> simp

theorem H_ket1_uniform (i : Fin 2) :
    prob (H ⬝ ket1) i = (1 / 2 : ℝ) := by
  fin_cases i <;> simp

@[simp]
theorem H2_mul_ket00 : H2 ⬝ ket00 = ketPlus ⊗ ketPlus := by
  rw [H2, ← ket0_kron_ket0, Matrix.kron_mul]
  change (H ⬝ ket0) ⊗ (H ⬝ ket0) = ketPlus ⊗ ketPlus
  simp

@[simp]
theorem H2_mul_ket01 : H2 ⬝ ket01 = ketPlus ⊗ ketMinus := by
  rw [H2, ← ket0_kron_ket1, Matrix.kron_mul]
  change (H ⬝ ket0) ⊗ (H ⬝ ket1) = ketPlus ⊗ ketMinus
  simp

@[simp]
theorem H2_mul_ket10 : H2 ⬝ ket10 = ketMinus ⊗ ketPlus := by
  rw [H2, ← ket1_kron_ket0, Matrix.kron_mul]
  change (H ⬝ ket1) ⊗ (H ⬝ ket0) = ketMinus ⊗ ketPlus
  simp

@[simp]
theorem H2_mul_ket11 : H2 ⬝ ket11 = ketMinus ⊗ ketMinus := by
  rw [H2, ← ket1_kron_ket1, Matrix.kron_mul]
  change (H ⬝ ket1) ⊗ (H ⬝ ket1) = ketMinus ⊗ ketMinus
  simp

theorem H2_ket00_uniform (i : Fin 4) :
    prob (H2 ⬝ ket00) i = (1 / 4 : ℝ) := by
  fin_cases i <;>
    simp [prob, Matrix.kron, ketPlus, finProdFinEquiv, Fin.divNat, Fin.modNat] <;>
    norm_num

theorem H2_ket01_uniform (i : Fin 4) :
    prob (H2 ⬝ ket01) i = (1 / 4 : ℝ) := by
  fin_cases i <;>
    simp [prob, Matrix.kron, ketPlus, ketMinus, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.normSq_neg] <;>
    norm_num

theorem H2_ket10_uniform (i : Fin 4) :
    prob (H2 ⬝ ket10) i = (1 / 4 : ℝ) := by
  fin_cases i <;>
    simp [prob, Matrix.kron, ketPlus, ketMinus, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.normSq_neg] <;>
    norm_num

theorem H2_ket11_uniform (i : Fin 4) :
    prob (H2 ⬝ ket11) i = (1 / 4 : ℝ) := by
  fin_cases i <;>
    simp [prob, Matrix.kron, ketMinus, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Complex.normSq_neg] <;>
    norm_num

end Theorems.RandomNumberGenerator

end Quantum
