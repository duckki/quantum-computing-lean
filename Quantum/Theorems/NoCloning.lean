import Quantum.Lemmas

namespace Quantum

namespace Theorems.NoCloning

theorem invSqrt2_ne_one_half : invSqrt2 ≠ (1 / 2 : ℂ) := by
  intro h
  have hnorm := congrArg Complex.normSq h
  norm_num at hnorm

private theorem ket0_inner_ketPlus :
    (ket0† ⬝ ketPlus) 0 0 = invSqrt2 := by
  norm_num [Matrix.mul, Matrix.adjoint, ket0, ketPlus, Vector.basis,
    _root_.Matrix.mul_apply, Fin.sum_univ_two]

private theorem ketZeros_isUnit (n : ℕ) : Matrix.isUnit (ketZeros n) := by
  simpa [ketZeros] using
    (Vector.basis_isUnit (⟨0, by simp⟩ : Fin (2 ^ n)))

private theorem ketZeros_inner_invSqrt2_smul (n : ℕ) :
    ((ketZeros n)† ⬝ (invSqrt2 • ketZeros n)) 0 0 = invSqrt2 := by
  have hunit : (ketZeros n)† ⬝ ketZeros n = (1 : Square 1) := by
    simpa [Matrix.isUnit] using ketZeros_isUnit n
  calc
    ((ketZeros n)† ⬝ (invSqrt2 • ketZeros n)) 0 0 =
        (invSqrt2 • ((ketZeros n)† ⬝ ketZeros n)) 0 0 := by
      simp [Matrix.mul]
    _ = invSqrt2 := by
      rw [hunit]
      simp

theorem no_cloning_of_inner_eq_invSqrt2 {d : ℕ} {x y blank : Vector d}
    (hblank : Matrix.isUnit blank) (hxy : (x† ⬝ y) 0 0 = invSqrt2) :
    ¬ (∃ U : Square (d * d),
      Matrix.isUnitary U ∧ ∀ s : Vector d, U ⬝ (s ⊗ blank) = s ⊗ s) := by
  rintro ⟨U, hU, hclone⟩
  have hUadj : U† ⬝ U = I (d * d) := by
    simpa using (Matrix.isUnitary_iff_adjoint_mul_self U).mp hU
  have hblankScalar : (blank† ⬝ blank) 0 0 = (1 : ℂ) := by
    have h := congrFun (congrFun hblank 0) 0
    simpa [Matrix.isUnit] using h
  let a : Vector (d * d) := x ⊗ blank
  let b : Vector (d * d) := y ⊗ blank
  have hpreserve :
      ((U ⬝ a)† ⬝ (U ⬝ b)) = (a† ⬝ b) := by
    calc
      ((U ⬝ a)† ⬝ (U ⬝ b)) = a† ⬝ ((U† ⬝ U) ⬝ b) := by
        simp [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_assoc]
      _ = a† ⬝ b := by
        rw [hUadj]
        simp [Matrix.mul]
  have hinner :
      ((x ⊗ x)† ⬝ (y ⊗ y)) =
        ((x ⊗ blank)† ⬝ (y ⊗ blank)) := by
    have hpreserve' :
        ((U ⬝ (x ⊗ blank))† ⬝ (U ⬝ (y ⊗ blank))) =
          ((x ⊗ blank)† ⬝ (y ⊗ blank)) := by
      simpa [a, b] using hpreserve
    rw [hclone x, hclone y] at hpreserve'
    exact hpreserve'
  have hscalar := congrFun (congrFun hinner 0) 0
  have hleft :
      ((x ⊗ x)† ⬝ (y ⊗ y)) 0 0 = (1 / 2 : ℂ) := by
    rw [Matrix.adjoint_kron, Matrix.kron_mul]
    simp [Matrix.kron, hxy, finProdFinEquiv, Fin.divNat, Fin.modNat, invSqrt2_mul_self]
  have hright :
      ((x ⊗ blank)† ⬝ (y ⊗ blank)) 0 0 = invSqrt2 := by
    rw [Matrix.adjoint_kron, Matrix.kron_mul]
    simp [Matrix.kron, hxy, hblankScalar, finProdFinEquiv, Fin.divNat, Fin.modNat]
  have hcontra : (1 / 2 : ℂ) = invSqrt2 := by
    rw [hleft, hright] at hscalar
    exact hscalar
  exact invSqrt2_ne_one_half hcontra.symm

/-- No unitary one-qubit gate with one blank ancilla can clone every qubit state. -/
theorem no_cloning_1 :
    ¬ (∃ U : Square 4,
      Matrix.isUnitary U ∧ ∀ s : Vector 2, U ⬝ (s ⊗ ket0) = s ⊗ s) := by
  exact no_cloning_of_inner_eq_invSqrt2 ket0_isUnit ket0_inner_ketPlus

/-- No unitary `n`-qubit gate with an all-zero blank register can clone every state vector. -/
theorem no_cloning_2 (n : ℕ) :
    ¬ (∃ U : Square (2 ^ n * 2 ^ n),
      Matrix.isUnitary U ∧ ∀ s : Vector (2 ^ n), U ⬝ (s ⊗ ketZeros n) = s ⊗ s) := by
  exact no_cloning_of_inner_eq_invSqrt2 (ketZeros_isUnit n)
    (ketZeros_inner_invSqrt2_smul n)

end Theorems.NoCloning

end Quantum
