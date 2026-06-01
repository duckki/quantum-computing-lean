import QuantumComputing.Notation

/-!
# No-Cloning Theorems

Formal statements showing that unitary cloning maps cannot exist for selected
families of pure states.
-/

namespace QuantumComputing

open scoped QuantumComputing

namespace Theorems.NoCloning

theorem invSqrt2_ne_one_half : √2⁻¹ ≠ (1 / 2 : ℂ) := by
  intro h
  have hnorm := congrArg Complex.normSq h
  norm_num at hnorm

private theorem ket0_inner_ketPlus :
    ((|0⟩)† ⬝ |+⟩) 0 0 = √2⁻¹ := by
  norm_num [Matrix.mul, Matrix.adjoint, ket0, ketPlus, Vector.basis,
    _root_.Matrix.mul_apply, Fin.sum_univ_two]

private theorem ketZeros_isNormalized (n : ℕ) : Vector.IsNormalized |0^n⟩ := by
  simpa [ketZeros] using
    (Vector.basis_isNormalized (⟨0, by simp⟩ : Fin (2 ^ n)))

private theorem ketZeros_inner_invSqrt2_smul (n : ℕ) :
    ((|0^n⟩)† ⬝ (√2⁻¹ • |0^n⟩)) 0 0 = √2⁻¹ := by
  have hunit : (|0^n⟩)† ⬝ |0^n⟩ = (1 : Square 1) := by
    simpa [Vector.IsNormalized] using ketZeros_isNormalized n
  calc
    ((|0^n⟩)† ⬝ (√2⁻¹ • |0^n⟩)) 0 0 =
        (√2⁻¹ • ((|0^n⟩)† ⬝ |0^n⟩)) 0 0 := by
      simp [Matrix.mul]
    _ = √2⁻¹ := by
      rw [hunit]
      simp

private theorem ketPlus_eq_superposition :
    |+⟩ = √2⁻¹ • |0⟩ + √2⁻¹ • |1⟩ := by
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
    (hblank : Vector.IsNormalized blank) (hxy : (x† ⬝ y) 0 0 = √2⁻¹) :
    ¬ (∃ U : Square (d * d),
      Matrix.isUnitary U ∧ ∀ s : Vector d, U ⬝ (s ⊗ blank) = s ⊗ s) := by
  rintro ⟨U, hU, hclone⟩
  have hUadj : U† ⬝ U = I (d * d) := by
    simpa using (Matrix.isUnitary_iff_adjoint_mul_self U).mp hU
  have hblankScalar : (blank† ⬝ blank) 0 0 = (1 : ℂ) := by
    have h := congrFun (congrFun hblank 0) 0
    simpa [Vector.IsNormalized] using h
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
      ((x ⊗ blank)† ⬝ (y ⊗ blank)) 0 0 = √2⁻¹ := by
    rw [Matrix.adjoint_kron, Matrix.kron_mul]
    simp [Matrix.kron, hxy, hblankScalar, finProdFinEquiv, Fin.divNat, Fin.modNat]
  have hcontra : (1 / 2 : ℂ) = √2⁻¹ := by
    rw [hleft, hright] at hscalar
    exact hscalar
  exact invSqrt2_ne_one_half hcontra.symm

/-- No unitary one-qubit gate with one blank ancilla can clone every qubit state. -/
theorem no_cloning_1 :
    ¬ (∃ U : Square 4,
      Matrix.isUnitary U ∧ ∀ s : Vector 2, U ⬝ (s ⊗ |0⟩) = s ⊗ s) := by
  exact no_cloning_of_inner_eq_invSqrt2 ket0_isNormalized ket0_inner_ketPlus

/-- No unitary `n`-qubit gate with an all-zero blank register can clone every state vector. -/
theorem no_cloning_2 (n : ℕ) :
    ¬ (∃ U : Square (2 ^ n * 2 ^ n),
      Matrix.isUnitary U ∧ ∀ s : Vector (2 ^ n), U ⬝ (s ⊗ |0^n⟩) = s ⊗ s) := by
  exact no_cloning_of_inner_eq_invSqrt2 (ketZeros_isNormalized n)
    (ketZeros_inner_invSqrt2_smul n)

/--
No unitary can clone an arbitrary one-qubit state into two copies while hiding
extra output in an arbitrary `n`-qubit garbage register.

The register dimension is written as `2 * (2 * 2 ^ n)` to match the tensor
shape used by the current API and avoid carrying arithmetic casts.
-/
theorem no_cloning_3 (n : ℕ) :
    ¬ (∃ (U : Square (2 * (2 * 2 ^ n))) (f : Vector 2 → Vector (2 ^ n)),
      Matrix.isUnitary U ∧
        ∀ s : Vector 2, Vector.IsNormalized s →
          U ⬝ (s ⊗ (|0⟩ ⊗ |0^n⟩)) = s ⊗ (s ⊗ f s)) := by
  rintro ⟨U, f, hU, hclone⟩
  let blank : Vector (2 * 2 ^ n) := |0⟩ ⊗ |0^n⟩
  have hblank : Vector.IsNormalized blank :=
    Vector.isNormalized_kron ket0_isNormalized (ketZeros_isNormalized n)
  have hlinear :
      U ⬝ (|+⟩ ⊗ blank) =
        √2⁻¹ • (U ⬝ (|0⟩ ⊗ blank)) +
          √2⁻¹ • (U ⬝ (|1⟩ ⊗ blank)) := by
    calc
      U ⬝ (|+⟩ ⊗ blank) =
          U ⬝ (((√2⁻¹ • |0⟩) + (√2⁻¹ • |1⟩)) ⊗ blank) := by
        rw [ketPlus_eq_superposition]
      _ = U ⬝ (√2⁻¹ • (|0⟩ ⊗ blank) + √2⁻¹ • (|1⟩ ⊗ blank)) := by
        rw [Matrix.kron_add_left, Matrix.kron_smul_left, Matrix.kron_smul_left]
      _ = √2⁻¹ • (U ⬝ (|0⟩ ⊗ blank)) +
            √2⁻¹ • (U ⬝ (|1⟩ ⊗ blank)) := by
        simp [Matrix.mul, _root_.Matrix.mul_add]
  have hstep :
      |+⟩ ⊗ (|+⟩ ⊗ f (|+⟩)) =
        √2⁻¹ • (|0⟩ ⊗ (|0⟩ ⊗ f (|0⟩))) +
          √2⁻¹ • (|1⟩ ⊗ (|1⟩ ⊗ f (|1⟩))) := by
    rw [← hclone |+⟩ ketPlus_isNormalized]
    rw [hlinear]
    rw [hclone |0⟩ ket0_isNormalized, hclone |1⟩ ket1_isNormalized]
  have hfzero : f (|+⟩) = 0 := by
    ext k j
    fin_cases j
    let idx : Fin (2 * (2 * 2 ^ n)) :=
      finProdFinEquiv ((0 : Fin 2), finProdFinEquiv ((1 : Fin 2), k))
    have hentry := congrFun (congrFun hstep idx) 0
    have hentry₀ : √2⁻¹ * (√2⁻¹ * f (|+⟩) k 0) = 0 := by
      simpa [idx, triple_kron_entry_010, ket0, ket1, ketPlus, Vector.basis] using hentry
    have hentry' : (1 / 2 : ℂ) * f (|+⟩) k 0 = 0 := by
      rw [← invSqrt2_mul_self]
      simpa only [mul_assoc] using hentry₀
    have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hentry').resolve_left hhalf
  have hinput : Vector.IsNormalized (|+⟩ ⊗ blank) :=
    Vector.isNormalized_kron ketPlus_isNormalized hblank
  have houtput : Vector.IsNormalized (U ⬝ (|+⟩ ⊗ blank)) :=
    Matrix.isUnitary_mul_isNormalized hU hinput
  have hzeroTensor :
      |+⟩ ⊗ (|+⟩ ⊗ (0 : Vector (2 ^ n))) =
        (0 : Vector (2 * (2 * 2 ^ n))) := by
    rw [Matrix.kron_zero_right]
    exact Matrix.kron_zero_right |+⟩
  rw [hclone |+⟩ ketPlus_isNormalized, hfzero, hzeroTensor] at houtput
  exact Vector.not_isNormalized_zero (2 * (2 * 2 ^ n)) houtput

end Theorems.NoCloning

end QuantumComputing
