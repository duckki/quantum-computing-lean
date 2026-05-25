import Quantum.Measurement.Computational
import Quantum.State

/-!
# Generalized Measurements

Complete families of measurement operators, generalized probabilities, and
post-measurement states.
-/

namespace Quantum

namespace Measurement

/-- A family of measurement operators is complete when the effects sum to identity. -/
def IsComplete {n outcomes : ℕ} (M : Fin outcomes → Square n) : Prop :=
  (∑ m : Fin outcomes, (M m)† ⬝ M m) = I n

/-- Probability of generalized measurement outcome `m` for measurement operators `M`. -/
noncomputable def generalizedProb {n outcomes : ℕ}
    (M : Fin outcomes → Square n) (s : Vector n) (m : Fin outcomes) : ℝ :=
  ((s† ⬝ ((M m)† ⬝ M m) ⬝ s) 0 0).re

/-- Normalized post-measurement state after generalized measurement outcome `m`. -/
noncomputable def generalizedPostMeasure {n outcomes : ℕ}
    (M : Fin outcomes → Square n) (s : Vector n) (m : Fin outcomes) : Vector n :=
  ((1 / Real.sqrt (generalizedProb M s m) : ℝ) : ℂ) • (M m ⬝ s)

/-- Generalized measurement operators satisfying the completeness condition. -/
structure Generalized (n outcomes : ℕ) where
  operator : Fin outcomes → Square n
  isComplete : IsComplete operator

theorem generalizedProb_eq_sum_prob {n outcomes : ℕ} (M : Fin outcomes → Square n)
    (s : Vector n) (m : Fin outcomes) :
    generalizedProb M s m = ∑ i : Fin n, prob (M m ⬝ s) i := by
  rw [sum_prob]
  have h : s† ⬝ ((M m)† ⬝ M m) ⬝ s = (M m ⬝ s)† ⬝ (M m ⬝ s) := by
    simp [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_assoc]
  simp [generalizedProb, h]

theorem generalizedProb_nonneg {n outcomes : ℕ} (M : Fin outcomes → Square n)
    (s : Vector n) (m : Fin outcomes) :
    0 ≤ generalizedProb M s m := by
  rw [generalizedProb_eq_sum_prob]
  exact Finset.sum_nonneg fun i _ => prob_nonneg _ _

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
    (hs : Vector.IsNormalized s) :
    (∑ m : Fin outcomes, generalizedProb M s m) = 1 := by
  rw [sum_generalizedProb, hM]
  have hroot : s† ⬝ s = 1 := by simpa [Vector.IsNormalized] using hs
  have h : s† ⬝ (I n) ⬝ s = 1 := by
    simpa [Matrix.mul] using hroot
  rw [h]
  norm_num

theorem projectors_isComplete (n : ℕ) : IsComplete (projectors n) := by
  exact sum_adjoint_mul_projectors n

namespace Generalized

variable {n outcomes : ℕ}

instance : CoeFun (Generalized n outcomes) (fun _ => Fin outcomes → Square n) where
  coe M := M.operator

@[simp]
theorem coe_apply (M : Generalized n outcomes) (m : Fin outcomes) :
    (M : Fin outcomes → Square n) m = M.operator m :=
  rfl

/-- Probability of generalized measurement outcome `m`. -/
noncomputable def prob (M : Generalized n outcomes) (s : Vector n) (m : Fin outcomes) : ℝ :=
  generalizedProb M.operator s m

/-- Normalized post-measurement state after generalized measurement outcome `m`. -/
noncomputable def postMeasure
    (M : Generalized n outcomes) (s : Vector n) (m : Fin outcomes) : Vector n :=
  generalizedPostMeasure M.operator s m

/-- Measurement probability for a pure state wrapper. -/
noncomputable def pureProb (M : Generalized n outcomes) (ψ : PureState n)
    (m : Fin outcomes) : ℝ :=
  M.prob ψ.vector m

/-- Post-measurement vector after measuring a pure state. -/
noncomputable def purePostMeasure (M : Generalized n outcomes) (ψ : PureState n)
    (m : Fin outcomes) : Vector n :=
  M.postMeasure ψ.vector m

@[simp]
theorem prob_eq_generalizedProb (M : Generalized n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    M.prob s m = generalizedProb M.operator s m :=
  rfl

@[simp]
theorem postMeasure_eq_generalizedPostMeasure (M : Generalized n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    M.postMeasure s m = generalizedPostMeasure M.operator s m :=
  rfl

theorem prob_nonneg (M : Generalized n outcomes)
    (s : Vector n) (m : Fin outcomes) :
    0 ≤ M.prob s m := by
  simpa [prob] using generalizedProb_nonneg M.operator s m

theorem sum_prob_of_isNormalized (M : Generalized n outcomes)
    {s : Vector n} (hs : Vector.IsNormalized s) :
    (∑ m : Fin outcomes, M.prob s m) = 1 := by
  simpa [prob] using sum_generalizedProb_of_isComplete M.isComplete hs

theorem sum_pureProb (M : Generalized n outcomes) (ψ : PureState n) :
    (∑ m : Fin outcomes, M.pureProb ψ m) = 1 := by
  simpa [pureProb] using M.sum_prob_of_isNormalized ψ.isNormalized

noncomputable def projective (n : ℕ) : Generalized n n where
  operator := projectors n
  isComplete := projectors_isComplete n

@[simp]
theorem projective_apply {n : ℕ} (i : Fin n) :
    (projective n).operator i = projectors n i :=
  rfl

end Generalized

@[simp]
theorem generalizedProb_projectors {n : ℕ} (s : Vector n) (i : Fin n) :
    generalizedProb (projectors n) s i = prob s i := by
  simp [generalizedProb, prob, projectors, quadratic_proj]

theorem sum_generalizedProb_projectors {n : ℕ} (s : Vector n) :
    (∑ i : Fin n, generalizedProb (projectors n) s i) = (∑ i : Fin n, prob s i) := by
  simp

theorem sum_generalizedProb_projectors_of_isNormalized {n : ℕ} {s : Vector n}
    (hs : Vector.IsNormalized s) :
    (∑ i : Fin n, generalizedProb (projectors n) s i) = 1 := by
  rw [sum_generalizedProb_projectors]
  exact sum_prob_of_isNormalized hs

@[simp]
theorem generalizedPostMeasure_projectors {n : ℕ} (s : Vector n) (i : Fin n) :
    generalizedPostMeasure (projectors n) s i = postMeasure s i := by
  simp [generalizedPostMeasure, postMeasure, generalizedProb, prob, projectors,
    quadratic_proj]

end Measurement

end Quantum
