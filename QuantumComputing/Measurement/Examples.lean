import QuantumComputing.Gates
import QuantumComputing.Measurement.Computational
import QuantumComputing.Measurement.PartialTrace
import QuantumComputing.State

/-!
# Measurement Examples

Concrete computational-basis measurement and partial-trace facts for the named
one- and two-qubit states.
-/

namespace QuantumComputing

namespace Measurement

@[simp]
theorem proj_zero : proj (0 : Fin 2) = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [proj, Matrix.proj, Matrix.mul, Matrix.adjoint, P0, Vector.basis,
      _root_.Matrix.mul_apply, Fin.sum_univ_one]

@[simp]
theorem proj_one : proj (1 : Fin 2) = P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [proj, Matrix.proj, Matrix.mul, Matrix.adjoint, P1, Vector.basis,
      _root_.Matrix.mul_apply, Fin.sum_univ_one]

@[simp]
theorem prob_ketPhiPlus_zero : prob ketPhiPlus 0 = (1 / 2 : ℝ) := by
  simp [prob, ketPhiPlus]

@[simp]
theorem prob_ketPhiPlus_one : prob ketPhiPlus 1 = 0 := by
  simp [prob, ketPhiPlus]

@[simp]
theorem prob_ketPhiPlus_two : prob ketPhiPlus 2 = 0 := by
  simp [prob, ketPhiPlus]

@[simp]
theorem prob_ketPhiPlus_three : prob ketPhiPlus 3 = (1 / 2 : ℝ) := by
  simp [prob, ketPhiPlus]

@[simp]
theorem postMeasure_ket0_zero : postMeasure ket0 0 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [postMeasure, prob, proj, Matrix.proj, Matrix.mul, Matrix.adjoint, ket0,
      Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem postMeasure_ket1_one : postMeasure ket1 1 = ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [postMeasure, prob, proj, Matrix.proj, Matrix.mul, Matrix.adjoint, ket1,
      Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem postMeasure_ketPlus_zero : postMeasure ketPlus 0 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [postMeasure, prob, proj, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ket0,
      Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem postMeasure_ketPlus_one : postMeasure ketPlus 1 = ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [postMeasure, prob, proj, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ket1,
      Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem postMeasure_ketMinus_zero : postMeasure ketMinus 0 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [postMeasure, prob, proj, Matrix.proj, Matrix.mul, Matrix.adjoint, ketMinus, ket0,
      Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem postMeasure_ketMinus_one : postMeasure ketMinus 1 = -ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [postMeasure, prob, proj, Matrix.proj, Matrix.mul, Matrix.adjoint, ketMinus, ket1,
      Vector.basis, _root_.Matrix.mul_apply]

@[simp]
theorem postMeasure_ketPhiPlus_zero : postMeasure ketPhiPlus 0 = ket00 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [postMeasure, prob, proj, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPhiPlus, ket00,
      Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_four]

@[simp]
theorem postMeasure_ketPhiPlus_three : postMeasure ketPhiPlus 3 = ket11 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [postMeasure, prob, proj, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPhiPlus, ket11,
      Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_four]

end Measurement

@[simp]
theorem partialTrace_proj_ket00 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket00) = P0 := by
  rw [← ket0_kron_ket0]
  rw [← proj_ket0]
  exact partialTrace_proj_kron_of_isNormalized (s := ket0) ket0_isNormalized

@[simp]
theorem partialTrace_proj_ket01 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket01) = P0 := by
  rw [← ket0_kron_ket1]
  rw [← proj_ket0]
  exact partialTrace_proj_kron_of_isNormalized (s := ket0) ket1_isNormalized

@[simp]
theorem partialTrace_proj_ket10 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket10) = P1 := by
  rw [← ket1_kron_ket0]
  rw [← proj_ket1]
  exact partialTrace_proj_kron_of_isNormalized (s := ket1) ket0_isNormalized

@[simp]
theorem partialTrace_proj_ket11 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket11) = P1 := by
  rw [← ket1_kron_ket1]
  rw [← proj_ket1]
  exact partialTrace_proj_kron_of_isNormalized (s := ket1) ket1_isNormalized

@[simp]
theorem partialTrace_proj_ketPhiPlus :
    partialTrace (n := 2) (m := 2) (Matrix.proj ketPhiPlus) = ((1 / 2 : ℂ) • (I 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTrace, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPhiPlus,
      _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_two]

@[simp]
theorem partialTrace_pure_ket00 :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ket00) = P0 := by
  simp [DensityMatrix.pure]

@[simp]
theorem partialTrace_pure_ket01 :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ket01) = P0 := by
  simp [DensityMatrix.pure]

@[simp]
theorem partialTrace_pure_ket10 :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ket10) = P1 := by
  simp [DensityMatrix.pure]

@[simp]
theorem partialTrace_pure_ket11 :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ket11) = P1 := by
  simp [DensityMatrix.pure]

@[simp]
theorem partialTrace_pure_ketPhiPlus :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ketPhiPlus) = ((1 / 2 : ℂ) • (I 2)) := by
  simp [DensityMatrix.pure]

end QuantumComputing
