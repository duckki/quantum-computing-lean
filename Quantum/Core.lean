import Mathlib.Data.Complex.BigOperators
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

theorem basis_isUnit (i : Fin n) : Matrix.isUnit (basis i) := by
  rw [Matrix.isUnit]
  ext j k
  fin_cases j
  fin_cases k
  simp [Matrix.mul, Matrix.adjoint, basis, _root_.Matrix.mul_apply]

end Vector

namespace Measurement

theorem proj_def {n : ℕ} (i : Fin n) :
    proj i = Matrix.proj (Vector.basis i) :=
  rfl

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

theorem sum_prob_of_isUnit {n : ℕ} {s : Vector n} (hs : Matrix.isUnit s) :
    (∑ i : Fin n, prob s i) = 1 := by
  rw [sum_prob]
  have hroot : s† ⬝ s = 1 := by simpa [Matrix.isUnit] using hs
  rw [hroot]
  norm_num

theorem exists_prob_ne_zero_of_isUnit {n : ℕ} {s : Vector n} (hs : Matrix.isUnit s) :
    ∃ i, prob s i ≠ 0 := by
  by_contra h
  have hzero : ∀ i, prob s i = 0 := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hsum_zero : (∑ i : Fin n, prob s i) = 0 := by
    simp [hzero]
  have hsum_one := sum_prob_of_isUnit hs
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
    (h : prob (s ⊗ u) = prob (t ⊗ u)) (hu : Matrix.isUnit u) :
    prob s = prob t := by
  funext i
  obtain ⟨j, hj⟩ := exists_prob_ne_zero_of_isUnit hu
  have hprob := congrFun h (finProdFinEquiv (i, j))
  rw [prob_kron_apply s u i j, prob_kron_apply t u i j] at hprob
  exact mul_right_cancel₀ hj hprob

theorem prob_kron_cancel_left {n m : ℕ} {s t : Vector n} {u : Vector m}
    (h : prob (u ⊗ s) = prob (u ⊗ t)) (hu : Matrix.isUnit u) :
    prob s = prob t := by
  funext i
  obtain ⟨j, hj⟩ := exists_prob_ne_zero_of_isUnit hu
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
  simpa [proj] using Matrix.proj_mul_proj_of_isUnit (Vector.basis_isUnit i)

@[simp]
theorem trace_proj {n : ℕ} (i : Fin n) : Tr(proj i) = 1 := by
  simpa [proj] using Matrix.trace_proj_of_isUnit (Vector.basis_isUnit i)

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

end Measurement

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

end Quantum
