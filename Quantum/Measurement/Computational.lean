import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.BigOperators
import Quantum.Matrix
import Quantum.States

/-!
# Computational-Basis Measurement

Projection operators, probabilities, post-measurement states, and reusable
facts for computational-basis measurement.
-/

namespace Quantum

namespace Measurement

/-- Projection onto the computational-basis outcome `i`. -/
noncomputable def proj {n : ℕ} (i : Fin n) : Square n :=
  Matrix.proj (Vector.basis i)

/-- Measurement operators for a computational-basis measurement. -/
noncomputable def projectors (n : ℕ) : Fin n → Square n :=
  fun i => proj i

/-- Probability of observing computational-basis outcome `i` when measuring `s`. -/
def prob {n : ℕ} (s : Vector n) (i : Fin n) : ℝ :=
  Complex.normSq (s i 0)

/-- Normalized post-measurement state after observing computational-basis outcome `i`. -/
noncomputable def postMeasure {n : ℕ} (s : Vector n) (i : Fin n) : Vector n :=
  ((1 / Real.sqrt (prob s i) : ℝ) : ℂ) • (proj i ⬝ s)

theorem proj_def {n : ℕ} (i : Fin n) :
    proj i = Matrix.proj (Vector.basis i) :=
  rfl

@[simp]
theorem prob_basis_self {n : ℕ} (i : Fin n) : prob (Vector.basis i) i = 1 := by
  simp [prob]

theorem prob_basis_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) :
    prob (Vector.basis i) j = 0 := by
  simp [prob, Vector.basis_apply_ne h]

theorem prob_nonneg {n : ℕ} (s : Vector n) (i : Fin n) : 0 ≤ prob s i :=
  Complex.normSq_nonneg _

theorem sum_prob {n : ℕ} (s : Vector n) :
    (∑ i : Fin n, prob s i) = ((s† ⬝ s) 0 0).re := by
  have h : (∑ i : Fin n, ((prob s i : ℝ) : ℂ)) = (s† ⬝ s) 0 0 := by
    simp [prob, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
      Complex.normSq_eq_conj_mul_self]
  simpa [Complex.re_sum] using congrArg Complex.re h

theorem sum_prob_of_isNormalized {n : ℕ} {s : Vector n} (hs : Vector.IsNormalized s) :
    (∑ i : Fin n, prob s i) = 1 := by
  rw [sum_prob]
  have hroot : s† ⬝ s = 1 := by simpa [Vector.IsNormalized] using hs
  rw [hroot]
  norm_num

theorem exists_prob_ne_zero_of_isNormalized {n : ℕ} {s : Vector n} (hs : Vector.IsNormalized s) :
    ∃ i, prob s i ≠ 0 := by
  by_contra h
  have hzero : ∀ i, prob s i = 0 := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hsum_zero : (∑ i : Fin n, prob s i) = 0 := by
    simp [hzero]
  have hsum_one := sum_prob_of_isNormalized hs
  rw [hsum_zero] at hsum_one
  norm_num at hsum_one

theorem prob_kron_apply {n m : ℕ} (s : Vector n) (t : Vector m)
    (i : Fin n) (j : Fin m) :
    prob (s ⊗ t) (finProdFinEquiv (i, j)) = prob s i * prob t j := by
  have hleft : (finProdFinEquiv.symm (0 : Fin (1 * 1))).1 = (0 : Fin 1) :=
    Subsingleton.elim _ _
  have hright : (finProdFinEquiv.symm (0 : Fin (1 * 1))).2 = (0 : Fin 1) :=
    Subsingleton.elim _ _
  simp [prob, Matrix.kron, Complex.normSq_mul, hleft, hright]

theorem prob_kron_cancel_right {n m : ℕ} {s t : Vector n} {u : Vector m}
    (h : prob (s ⊗ u) = prob (t ⊗ u)) (hu : Vector.IsNormalized u) :
    prob s = prob t := by
  funext i
  obtain ⟨j, hj⟩ := exists_prob_ne_zero_of_isNormalized hu
  have hprob := congrFun h (finProdFinEquiv (i, j))
  rw [prob_kron_apply s u i j, prob_kron_apply t u i j] at hprob
  exact mul_right_cancel₀ hj hprob

theorem prob_kron_cancel_left {n m : ℕ} {s t : Vector n} {u : Vector m}
    (h : prob (u ⊗ s) = prob (u ⊗ t)) (hu : Vector.IsNormalized u) :
    prob s = prob t := by
  funext i
  obtain ⟨j, hj⟩ := exists_prob_ne_zero_of_isNormalized hu
  have hprob := congrFun h (finProdFinEquiv (j, i))
  rw [prob_kron_apply u s j i, prob_kron_apply u t j i] at hprob
  exact mul_left_cancel₀ hj hprob

theorem prob_add_of_pointwise_orthogonal {n : ℕ} {s t : Vector n}
    (h : ∀ i, star (s i 0) * t i 0 = 0) :
    prob (s + t) = fun i => prob s i + prob t i := by
  funext i
  have hinner : (star (s i 0) * t i 0).re = 0 := by
    simpa using congrArg Complex.re (h i)
  have hdot : (s i 0).re * (t i 0).re + (s i 0).im * (t i 0).im = 0 := by
    simpa [Complex.mul_re, Complex.conj_re, Complex.conj_im] using hinner
  simp [prob, Complex.normSq_add, hdot]

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

theorem quadratic_proj {n : ℕ} (s : Vector n) (i : Fin n) :
    ((s† ⬝ proj i ⬝ s) 0 0).re = Complex.normSq (s i 0) := by
  simp [proj, Matrix.proj, Matrix.mul, Matrix.adjoint, Vector.basis,
    _root_.Matrix.mul_apply, Complex.normSq]

@[simp]
theorem adjoint_proj {n : ℕ} (i : Fin n) :
    (proj i)† = proj i := by
  simp [proj]

@[simp]
theorem proj_mul_self {n : ℕ} (i : Fin n) :
    proj i ⬝ proj i = proj i := by
  simpa [proj] using Matrix.proj_mul_proj_of_isNormalized (Vector.basis_isNormalized i)

@[simp]
theorem trace_proj {n : ℕ} (i : Fin n) : Tr(proj i) = 1 := by
  simpa [proj] using Matrix.trace_proj_of_isNormalized (Vector.basis_isNormalized i)

@[simp]
theorem adjoint_mul_proj {n : ℕ} (i : Fin n) :
    (proj i)† ⬝ proj i = proj i := by
  simp

@[simp]
theorem proj_mul_proj_ne {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    proj i ⬝ proj j = 0 := by
  ext a b
  simp [proj, Matrix.proj, Matrix.mul, Matrix.adjoint, Vector.basis,
    _root_.Matrix.mul_apply, Ne.symm h]

theorem proj_mul_proj {n : ℕ} (i j : Fin n) :
    proj i ⬝ proj j = if i = j then proj i else 0 := by
  by_cases h : i = j
  · subst j
    simp
  · simp [h, proj_mul_proj_ne h]

@[simp]
theorem sum_proj (n : ℕ) : (∑ i : Fin n, proj i) = I n := by
  ext a b
  rw [_root_.Matrix.sum_apply]
  simp [proj, Matrix.proj, Matrix.mul, Matrix.adjoint, Vector.basis,
    _root_.Matrix.mul_apply, _root_.Matrix.one_apply]

@[simp]
theorem sum_adjoint_mul_projectors (n : ℕ) :
    (∑ i : Fin n, (projectors n i)† ⬝ projectors n i) = I n := by
  simp [projectors]

end Measurement

end Quantum
