import Quantum.Measurement
import Quantum.Lemmas.Core

namespace Quantum

namespace Measurement

theorem sum_generalizedProb {n outcomes : ℕ} (M : Fin outcomes → Square n) (s : Vector n) :
    (∑ m : Fin outcomes, generalizedProb M s m) =
      ((s† ⬝ (∑ m : Fin outcomes, (M m)† ⬝ M m) ⬝ s) 0 0).re := by
  have hmat :
      s† ⬝ (∑ m : Fin outcomes, (M m)† ⬝ M m) ⬝ s =
        ∑ m : Fin outcomes, s† ⬝ ((M m)† ⬝ M m) ⬝ s := by
    simp [Matrix.mul, _root_.Matrix.mul_sum, _root_.Matrix.sum_mul]
  have hscalar :
      (∑ m : Fin outcomes, (s† ⬝ ((M m)† ⬝ M m) ⬝ s) 0 0) =
        (s† ⬝ (∑ m : Fin outcomes, (M m)† ⬝ M m) ⬝ s) 0 0 := by
    simpa [_root_.Matrix.sum_apply] using congr_fun (congr_fun hmat.symm 0) 0
  simpa [generalizedProb, Complex.re_sum] using congrArg Complex.re hscalar

theorem sum_generalizedProb_of_isComplete {n outcomes : ℕ}
    {M : Fin outcomes → Square n} (hM : IsComplete M) {s : Vector n}
    (hs : Matrix.isUnit s) :
    (∑ m : Fin outcomes, generalizedProb M s m) = 1 := by
  rw [sum_generalizedProb, hM]
  have hroot : s† ⬝ s = 1 := by simpa [Matrix.isUnit] using hs
  have h : s† ⬝ (I n) ⬝ s = 1 := by
    simpa [Matrix.mul] using hroot
  rw [h]
  norm_num

theorem projectors_isComplete (n : ℕ) : IsComplete (projectors n) := by
  exact sum_adjoint_mul_projectors n

@[simp]
theorem projectiveOperators_apply {n outcomes : ℕ}
    (u : Fin outcomes → Vector n) (i : Fin outcomes) :
    projectiveOperators u i = Matrix.proj (u i) :=
  rfl

theorem generalizedProb_projectiveOperators_of_isUnit {n outcomes : ℕ}
    {u : Fin outcomes → Vector n} (s : Vector n) {i : Fin outcomes}
    (hu : Matrix.isUnit (u i)) :
    generalizedProb (projectiveOperators u) s i = projProb u s i := by
  simp [generalizedProb, projProb, projectiveOperators, Matrix.proj_mul_proj_of_isUnit hu]

theorem generalizedPostMeasure_projectiveOperators_of_isUnit {n outcomes : ℕ}
    {u : Fin outcomes → Vector n} (s : Vector n) {i : Fin outcomes}
    (hu : Matrix.isUnit (u i)) :
    generalizedPostMeasure (projectiveOperators u) s i = projPostMeasure u s i := by
  simp [generalizedPostMeasure, projPostMeasure, projectiveOperators,
    generalizedProb_projectiveOperators_of_isUnit s hu]

theorem projectiveOperators_eq_projectors (n : ℕ) :
    projectiveOperators (fun i : Fin n => Vector.basis i) = projectors n :=
  rfl

theorem projectiveOperators_computationalBasis_isComplete (n : ℕ) :
    IsProjectiveComplete (fun i : Fin n => Vector.basis i) := by
  simpa [projectiveOperators_eq_projectors] using projectors_isComplete n

namespace Generalized

@[simp]
theorem prob_eq_generalizedProb {n outcomes : ℕ} (M : Generalized n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    M.prob s m = generalizedProb M.operator s m :=
  rfl

@[simp]
theorem postMeasure_eq_generalizedPostMeasure {n outcomes : ℕ} (M : Generalized n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    M.postMeasure s m = generalizedPostMeasure M.operator s m :=
  rfl

theorem prob_nonneg {n outcomes : ℕ} (M : Generalized n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    0 ≤ M.prob s m := by
  simpa [prob] using generalizedProb_nonneg M.operator s m

theorem sum_prob_of_isUnit {n outcomes : ℕ} (M : Generalized n outcomes)
    {s : Vector n} (hs : Matrix.isUnit s) :
    (∑ m : Fin outcomes, M.prob s m) = 1 := by
  simpa [prob] using sum_generalizedProb_of_isComplete M.isComplete hs

theorem sum_pureProb {n outcomes : ℕ} (M : Generalized n outcomes) (ψ : PureState n) :
    (∑ m : Fin outcomes, M.pureProb ψ m) = 1 := by
  simpa [pureProb] using M.sum_prob_of_isUnit ψ.isUnit

noncomputable def projective (n : ℕ) : Generalized n n where
  operator := projectors n
  isComplete := projectors_isComplete n

@[simp]
theorem projective_apply {n : ℕ} (i : Fin n) :
    (projective n).operator i = projectors n i :=
  rfl

end Generalized

namespace Projective

@[simp]
theorem operator_apply {n outcomes : ℕ} (M : Projective n outcomes) (m : Fin outcomes) :
    M.operator m = Matrix.proj (M.vector m) :=
  rfl

@[simp]
theorem toGeneralized_operator {n outcomes : ℕ} (M : Projective n outcomes) :
    M.toGeneralized.operator = M.operator :=
  rfl

@[simp]
theorem prob_eq_projProb {n outcomes : ℕ} (M : Projective n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    M.prob s m = projProb M.vector s m :=
  rfl

@[simp]
theorem postMeasure_eq_projPostMeasure {n outcomes : ℕ} (M : Projective n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    M.postMeasure s m = projPostMeasure M.vector s m :=
  rfl

@[simp]
theorem prob_eq_generalized_prob {n outcomes : ℕ} (M : Projective n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    M.prob s m = M.toGeneralized.prob s m :=
  (generalizedProb_projectiveOperators_of_isUnit s (M.isUnit m)).symm

@[simp]
theorem postMeasure_eq_generalizedPostMeasure {n outcomes : ℕ} (M : Projective n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    M.postMeasure s m = M.toGeneralized.postMeasure s m :=
  (generalizedPostMeasure_projectiveOperators_of_isUnit s (M.isUnit m)).symm

theorem sum_prob_of_isUnit {n outcomes : ℕ} (M : Projective n outcomes)
    {s : Vector n} (hs : Matrix.isUnit s) :
    (∑ m : Fin outcomes, M.prob s m) = 1 := by
  calc
    (∑ m : Fin outcomes, M.prob s m) = ∑ m : Fin outcomes, M.toGeneralized.prob s m := by
      apply Finset.sum_congr rfl
      intro m _
      exact M.prob_eq_generalized_prob s m
    _ = 1 := M.toGeneralized.sum_prob_of_isUnit hs

noncomputable def computationalBasis (n : ℕ) : Projective n n where
  vector := fun i => Vector.basis i
  isUnit := fun i => Vector.basis_isUnit i
  isComplete := projectiveOperators_computationalBasis_isComplete n

@[simp]
theorem computationalBasis_apply {n : ℕ} (i : Fin n) :
    (computationalBasis n).vector i = Vector.basis i :=
  rfl

end Projective

theorem projProb_eq_quadratic_projector {n outcomes : ℕ}
    (u : Fin outcomes → Vector n) (s : Vector n) (i : Fin outcomes) :
    projProb u s i = ((s† ⬝ Matrix.proj (u i) ⬝ s) 0 0).re := by
  simp [projProb]

theorem projective_quadratic_eq_inner_square {n outcomes : ℕ}
    (u : Fin outcomes → Vector n) (s : Vector n) (i : Fin outcomes) :
    s† ⬝ Matrix.proj (u i) ⬝ s = ((u i)† ⬝ s)† ⬝ ((u i)† ⬝ s) := by
  simp [Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_assoc]

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
