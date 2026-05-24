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

@[simp]
theorem P0_mul_ket0 : P0 ⬝ ket0 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P0, ket0, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P0_mul_ket1 : P0 ⬝ ket1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P0, ket1, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P1_mul_ket0 : P1 ⬝ ket0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P1, ket0, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P1_mul_ket1 : P1 ⬝ ket1 = ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P1, ket1, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem PPlus_mul_ketPlus : PPlus ⬝ ketPlus = ketPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, _root_.Matrix.mul_apply]

@[simp]
theorem PPlus_mul_ketMinus : PPlus ⬝ ketMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply]

@[simp]
theorem PMinus_mul_ketPlus : PMinus ⬝ ketPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply]

@[simp]
theorem PMinus_mul_ketMinus : PMinus ⬝ ketMinus = ketMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketMinus, _root_.Matrix.mul_apply] <;>
    ring_nf

@[simp]
theorem PPlus_adjoint : PPlus† = PPlus := by
  simp [PPlus]

@[simp]
theorem PMinus_adjoint : PMinus† = PMinus := by
  simp [PMinus]

@[simp]
theorem PPlus_mul_self : PPlus ⬝ PPlus = PPlus := by
  simpa [PPlus] using Matrix.proj_mul_proj_of_isUnit ketPlus_isUnit

@[simp]
theorem PMinus_mul_self : PMinus ⬝ PMinus = PMinus := by
  simpa [PMinus] using Matrix.proj_mul_proj_of_isUnit ketMinus_isUnit

@[simp]
theorem trace_PPlus : Tr(PPlus) = 1 := by
  simpa [PPlus] using Matrix.trace_proj_of_isUnit ketPlus_isUnit

@[simp]
theorem trace_PMinus : Tr(PMinus) = 1 := by
  simpa [PMinus] using Matrix.trace_proj_of_isUnit ketMinus_isUnit

@[simp]
theorem PPlus_mul_PMinus : PPlus ⬝ PMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem PMinus_mul_PPlus : PMinus ⬝ PPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem PPlus_add_PMinus : PPlus + PMinus = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply] <;>
    ring_nf

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
theorem X_adjoint : X† = X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, X]

@[simp]
theorem Z_adjoint : Z† = Z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, Z]

@[simp]
theorem H_adjoint : H† = H := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, H]

@[simp]
theorem CNOT_adjoint : CNOT† = CNOT := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, CNOT]

@[simp]
theorem CZ_adjoint : CZ† = CZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, CZ]

@[simp]
theorem SWAP_adjoint : SWAP† = SWAP := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, SWAP]

@[simp]
theorem X_mul_self : X ⬝ X = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, X, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Z_mul_self : Z ⬝ Z = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Z, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem H_mul_self : H ⬝ H = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem CNOT_mul_self : CNOT ⬝ CNOT = I 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, CNOT, _root_.Matrix.mul_apply, Fin.sum_univ_four] <;> decide

@[simp]
theorem CZ_mul_self : CZ ⬝ CZ = I 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, CZ, _root_.Matrix.mul_apply, Fin.sum_univ_four] <;> decide

@[simp]
theorem SWAP_mul_self : SWAP ⬝ SWAP = I 4 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, SWAP, _root_.Matrix.mul_apply, Fin.sum_univ_four] <;> decide

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
theorem X_mul_ketPlus : X ⬝ ketPlus = ketPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, X, ketPlus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem X_mul_ketMinus : X ⬝ ketMinus = -ketMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, X, ketMinus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Z_mul_ketPlus : Z ⬝ ketPlus = ketMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Z, ketPlus, ketMinus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem Z_mul_ketMinus : Z ⬝ ketMinus = ketPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, Z, ketPlus, ketMinus, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem H_mul_ketPlus : H ⬝ ketPlus = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, ketPlus, ket0, Vector.basis, _root_.Matrix.mul_apply,
      Fin.sum_univ_two]

@[simp]
theorem H_mul_ketMinus : H ⬝ ketMinus = ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, H, ketMinus, ket1, Vector.basis, _root_.Matrix.mul_apply,
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
