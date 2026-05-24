import Quantum.Lemmas.Core

namespace Quantum

namespace Measurement

@[simp]
theorem prob_ketPlus_zero : prob ketPlus 0 = (1 / 2 : ℝ) := by
  simp [prob, ketPlus]

@[simp]
theorem prob_ketPlus_one : prob ketPlus 1 = (1 / 2 : ℝ) := by
  simp [prob, ketPlus]

@[simp]
theorem prob_ketMinus_zero : prob ketMinus 0 = (1 / 2 : ℝ) := by
  simp [prob, ketMinus]

@[simp]
theorem prob_ketMinus_one : prob ketMinus 1 = (1 / 2 : ℝ) := by
  simp [prob, ketMinus, Complex.normSq_neg]

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

@[simp]
theorem generalizedProb_projectors {n : ℕ} (s : Vector n) (i : Fin n) :
    generalizedProb (projectors n) s i = prob s i := by
  simp [generalizedProb, prob, projectors, quadratic_proj]

theorem sum_generalizedProb_projectors {n : ℕ} (s : Vector n) :
    (∑ i : Fin n, generalizedProb (projectors n) s i) = (∑ i : Fin n, prob s i) := by
  simp

theorem sum_generalizedProb_projectors_of_isUnit {n : ℕ} {s : Vector n}
    (hs : Matrix.isUnit s) :
    (∑ i : Fin n, generalizedProb (projectors n) s i) = 1 := by
  rw [sum_generalizedProb_projectors]
  exact sum_prob_of_isUnit hs

@[simp]
theorem generalizedPostMeasure_projectors {n : ℕ} (s : Vector n) (i : Fin n) :
    generalizedPostMeasure (projectors n) s i = postMeasure s i := by
  simp [generalizedPostMeasure, postMeasure, generalizedProb, prob, projectors,
    quadratic_proj]

end Measurement

end Quantum
