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

private theorem Matrix.isUnit_kron {m n : ℕ} {s : Vector m} {t : Vector n}
    (hs : Matrix.isUnit s) (ht : Matrix.isUnit t) : Matrix.isUnit (s ⊗ t) := by
  rw [Matrix.isUnit, Matrix.adjoint_kron, Matrix.kron_mul]
  have hs' : s† ⬝ s = (1 : Square 1) := by
    simpa [Matrix.isUnit] using hs
  have ht' : t† ⬝ t = (1 : Square 1) := by
    simpa [Matrix.isUnit] using ht
  rw [hs', ht']
  simp

private theorem Matrix.not_isUnit_zero (n : ℕ) : ¬ Matrix.isUnit (0 : Vector n) := by
  intro h
  have hscalar := congrFun (congrFun h 0) 0
  norm_num [Matrix.isUnit, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply] at hscalar

private theorem Matrix.kron_add_left {m n p q : ℕ}
    (A B : Matrix m n) (C : Matrix p q) :
    (A + B) ⊗ C = A ⊗ C + B ⊗ C := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [Matrix.kron, add_mul]

private theorem Matrix.kron_smul_left {m n p q : ℕ}
    (a : ℂ) (A : Matrix m n) (C : Matrix p q) :
    (a • A) ⊗ C = a • (A ⊗ C) := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [Matrix.kron, mul_assoc]

private theorem Matrix.kron_zero_right {m n p q : ℕ} (A : Matrix m n) :
    A ⊗ (0 : Matrix p q) = 0 := by
  ext i j
  rcases finProdFinEquiv.symm i with ⟨i₁, i₂⟩
  rcases finProdFinEquiv.symm j with ⟨j₁, j₂⟩
  simp [Matrix.kron]

private theorem ketPlus_eq_superposition :
    ketPlus = invSqrt2 • ket0 + invSqrt2 • ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ketPlus, ket0, ket1, Vector.basis]

private theorem triple_kron_entry_010 {n : ℕ} (a b : Vector 2) (c : Vector (2 ^ n))
    (k : Fin (2 ^ n)) :
    (a ⊗ (b ⊗ c))
        (finProdFinEquiv ((0 : Fin 2), finProdFinEquiv ((1 : Fin 2), k))) 0 =
      a 0 0 * (b 1 0 * c k 0) := by
  change
    (a ⊗ (b ⊗ c))
        (finProdFinEquiv ((0 : Fin 2), finProdFinEquiv ((1 : Fin 2), k)))
        (finProdFinEquiv ((0 : Fin 1), finProdFinEquiv ((0 : Fin 1), (0 : Fin 1)))) =
      a 0 0 * (b 1 0 * c k 0)
  rw [Matrix.kron_apply, Matrix.kron_apply]

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

private theorem no_cloning_with_garbage_core (n : ℕ) :
    ¬ (∃ (U : Square (2 * (2 * 2 ^ n))) (f : Vector 2 → Vector (2 ^ n)),
      Matrix.isUnitary U ∧
        ∀ s : Vector 2, Matrix.isUnit s →
          U ⬝ (s ⊗ (ket0 ⊗ ketZeros n)) = s ⊗ (s ⊗ f s)) := by
  rintro ⟨U, f, hU, hclone⟩
  let blank : Vector (2 * 2 ^ n) := ket0 ⊗ ketZeros n
  have hblank : Matrix.isUnit blank :=
    Matrix.isUnit_kron ket0_isUnit (ketZeros_isUnit n)
  have hlinear :
      U ⬝ (ketPlus ⊗ blank) =
        invSqrt2 • (U ⬝ (ket0 ⊗ blank)) +
          invSqrt2 • (U ⬝ (ket1 ⊗ blank)) := by
    calc
      U ⬝ (ketPlus ⊗ blank) =
          U ⬝ (((invSqrt2 • ket0) + (invSqrt2 • ket1)) ⊗ blank) := by
        rw [ketPlus_eq_superposition]
      _ = U ⬝ (invSqrt2 • (ket0 ⊗ blank) + invSqrt2 • (ket1 ⊗ blank)) := by
        rw [Matrix.kron_add_left, Matrix.kron_smul_left, Matrix.kron_smul_left]
      _ = invSqrt2 • (U ⬝ (ket0 ⊗ blank)) +
            invSqrt2 • (U ⬝ (ket1 ⊗ blank)) := by
        simp [Matrix.mul, _root_.Matrix.mul_add]
  have hstep :
      ketPlus ⊗ (ketPlus ⊗ f ketPlus) =
        invSqrt2 • (ket0 ⊗ (ket0 ⊗ f ket0)) +
          invSqrt2 • (ket1 ⊗ (ket1 ⊗ f ket1)) := by
    rw [← hclone ketPlus ketPlus_isUnit]
    rw [hlinear]
    rw [hclone ket0 ket0_isUnit, hclone ket1 ket1_isUnit]
  have hfzero : f ketPlus = 0 := by
    ext k j
    fin_cases j
    let idx : Fin (2 * (2 * 2 ^ n)) :=
      finProdFinEquiv ((0 : Fin 2), finProdFinEquiv ((1 : Fin 2), k))
    have hentry := congrFun (congrFun hstep idx) 0
    have hentry₀ : invSqrt2 * (invSqrt2 * f ketPlus k 0) = 0 := by
      simpa [idx, triple_kron_entry_010, ket0, ket1, ketPlus, Vector.basis] using hentry
    have hentry' : (1 / 2 : ℂ) * f ketPlus k 0 = 0 := by
      rw [← invSqrt2_mul_self]
      simpa only [mul_assoc] using hentry₀
    have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hentry').resolve_left hhalf
  have hinput : Matrix.isUnit (ketPlus ⊗ blank) :=
    Matrix.isUnit_kron ketPlus_isUnit hblank
  have houtput : Matrix.isUnit (U ⬝ (ketPlus ⊗ blank)) :=
    Matrix.isUnitary_mul_isUnit hU hinput
  have hzeroTensor :
      ketPlus ⊗ (ketPlus ⊗ (0 : Vector (2 ^ n))) =
        (0 : Vector (2 * (2 * 2 ^ n))) := by
    rw [Matrix.kron_zero_right]
    exact Matrix.kron_zero_right ketPlus
  rw [hclone ketPlus ketPlus_isUnit, hfzero, hzeroTensor] at houtput
  exact Matrix.not_isUnit_zero (2 * (2 * 2 ^ n)) houtput

/--
No unitary can clone an arbitrary one-qubit state into two copies while hiding
extra output in an arbitrary `n`-qubit garbage register.

The register dimension is written as `2 * (2 * 2 ^ n)` to match the tensor
shape used by the current API and avoid carrying arithmetic casts.
-/
theorem no_cloning_3 (n : ℕ) :
    ¬ (∃ (U : Square (2 * (2 * 2 ^ n))) (f : Vector 2 → Vector (2 ^ n)),
      Matrix.isUnitary U ∧
        ∀ s : Vector 2, Matrix.isUnit s →
          U ⬝ (s ⊗ (ket0 ⊗ ketZeros n)) = s ⊗ (s ⊗ f s)) := by
  exact no_cloning_with_garbage_core n

/--
Alternative no-cloning formulation with an explicit garbage register. This has
the same statement as `no_cloning_3`; the current proof uses the old
partial-measurement contradiction specialized to a single amplitude.
-/
theorem no_cloning_3_alt (n : ℕ) :
    ¬ (∃ (U : Square (2 * (2 * 2 ^ n))) (f : Vector 2 → Vector (2 ^ n)),
      Matrix.isUnitary U ∧
        ∀ s : Vector 2, Matrix.isUnit s →
          U ⬝ (s ⊗ (ket0 ⊗ ketZeros n)) = s ⊗ (s ⊗ f s)) := by
  exact no_cloning_with_garbage_core n

end Theorems.NoCloning

end Quantum
