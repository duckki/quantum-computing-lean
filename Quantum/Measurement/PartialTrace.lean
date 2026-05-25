import Quantum.Measurement.Computational

/-!
# Partial Trace

Partial trace over a tensor factor and probability lemmas for measuring a
subsystem.
-/

namespace Quantum

noncomputable def partialTrace {n m : ℕ} (A : Square (n * m)) : Square n :=
  fun i j => ∑ k : Fin m, A (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))

namespace Measurement

/-- Probability of measuring outcome `i` on the first subsystem after tracing out the second. -/
noncomputable def partialProb {n m : ℕ} (s : Vector (n * m)) (i : Fin n) : ℝ :=
  ((partialTrace (n := n) (m := m) (Matrix.proj s)) i i).re

end Measurement

@[simp]
theorem partialTrace_zero {n m : ℕ} :
    partialTrace (n := n) (m := m) (0 : Square (n * m)) = 0 := by
  ext i j
  simp [partialTrace]

@[simp]
theorem partialTrace_add {n m : ℕ} (A B : Square (n * m)) :
    partialTrace (n := n) (m := m) (A + B) =
      partialTrace (n := n) (m := m) A + partialTrace (n := n) (m := m) B := by
  ext i j
  simp [partialTrace, Finset.sum_add_distrib]

@[simp]
theorem partialTrace_sub {n m : ℕ} (A B : Square (n * m)) :
    partialTrace (n := n) (m := m) (A - B) =
      partialTrace (n := n) (m := m) A - partialTrace (n := n) (m := m) B := by
  ext i j
  simp [partialTrace, Finset.sum_sub_distrib]

theorem partialTrace_smul {n m : ℕ} (a : ℂ) (A : Square (n * m)) :
    partialTrace (n := n) (m := m) (a • A) =
      a • partialTrace (n := n) (m := m) A := by
  ext i j
  simp [partialTrace, Finset.mul_sum]

@[simp]
theorem trace_partialTrace {n m : ℕ} (A : Square (n * m)) :
    Matrix.trace (partialTrace (n := n) (m := m) A) = Matrix.trace A := by
  have h :=
    Fintype.sum_equiv finProdFinEquiv
      (fun x : Fin n × Fin m => A (finProdFinEquiv x) (finProdFinEquiv x))
      (fun x : Fin (n * m) => A x x)
      (by intro x; simp)
  calc
    Matrix.trace (partialTrace (n := n) (m := m) A) =
        ∑ x : Fin n × Fin m, A (finProdFinEquiv x) (finProdFinEquiv x) := by
      simp [Matrix.trace, _root_.Matrix.trace, partialTrace, Fintype.sum_prod_type]
    _ = Matrix.trace A := by
      simpa [Matrix.trace, _root_.Matrix.trace] using h

@[simp]
theorem partialTrace_kron {n m : ℕ} (A : Square n) (B : Square m) :
    partialTrace (n := n) (m := m) (A ⊗ B) = Matrix.trace B • A := by
  ext i j
  simp [partialTrace, Matrix.kron, Matrix.trace, _root_.Matrix.trace]
  rw [mul_comm]
  rw [Finset.mul_sum]

theorem partialTrace_kron_eq_of_trace_eq {n m : ℕ} (A : Square n) {B C : Square m}
    (h : Matrix.trace B = Matrix.trace C) :
    partialTrace (n := n) (m := m) (A ⊗ B) =
      partialTrace (n := n) (m := m) (A ⊗ C) := by
  rw [partialTrace_kron, partialTrace_kron, h]

theorem partialTrace_add_kron {n m : ℕ} (A B : Square n) (C D : Square m) :
    partialTrace (n := n) (m := m) (A ⊗ C + B ⊗ D) =
      Matrix.trace C • A + Matrix.trace D • B := by
  simp

theorem partialTrace_add_kron_four {n m : ℕ}
    (A B C D : Square n) (V W X Y : Square m) :
    partialTrace (n := n) (m := m) (A ⊗ V + B ⊗ W + C ⊗ X + D ⊗ Y) =
      Matrix.trace V • A + Matrix.trace W • B + Matrix.trace X • C + Matrix.trace Y • D := by
  simp

@[simp]
theorem partialTrace_kron_proj_of_isNormalized {n m : ℕ} (A : Square n) {s : Vector m}
    (hs : Vector.IsNormalized s) :
    partialTrace (n := n) (m := m) (A ⊗ Matrix.proj s) = A := by
  rw [partialTrace_kron, Matrix.trace_proj_of_isNormalized hs]
  simp

@[simp]
theorem partialTrace_proj_kron_of_isNormalized {n m : ℕ} (s : Vector n) {t : Vector m}
    (ht : Vector.IsNormalized t) :
    partialTrace (n := n) (m := m) (Matrix.proj (s ⊗ t)) = Matrix.proj s := by
  rw [Matrix.proj_kron]
  exact partialTrace_kron_proj_of_isNormalized (Matrix.proj s) ht

theorem partialTrace_proj_eq_of_kron_eq {n m : ℕ} {a b : Vector n} {s t : Vector m}
    (h : a ⊗ s = b ⊗ t) (hs : Vector.IsNormalized s) (ht : Vector.IsNormalized t) :
    Matrix.proj a = Matrix.proj b := by
  have hpartial :
      partialTrace (n := n) (m := m) (Matrix.proj (a ⊗ s)) =
        partialTrace (n := n) (m := m) (Matrix.proj (b ⊗ t)) := by
    rw [h]
  rw [partialTrace_proj_kron_of_isNormalized (s := a) hs] at hpartial
  rw [partialTrace_proj_kron_of_isNormalized (s := b) ht] at hpartial
  exact hpartial

theorem partialTrace_proj_add_kron_of_inner_eq_one {n m : ℕ}
    (t p : Vector n) {w q : Vector m}
    (hw : Vector.IsNormalized w) (hq : Vector.IsNormalized q) (h : w† ⬝ q = 1) :
    partialTrace (n := n) (m := m) (Matrix.proj ((t ⊗ w) + (p ⊗ q))) =
      Matrix.proj (t + p) := by
  have hqw : Matrix.trace (q ⬝ w†) = 1 := by
    rw [Matrix.trace_outer_eq_inner, h]
    simp
  have hwq_inner : q† ⬝ w = 1 := by
    have hadj := congrArg Matrix.adjoint h
    simpa using hadj
  have hwq : Matrix.trace (w ⬝ q†) = 1 := by
    rw [Matrix.trace_outer_eq_inner, hwq_inner]
    simp
  rw [Matrix.proj_add_kron, partialTrace_add_kron_four,
    Matrix.trace_proj_of_isNormalized hw, Matrix.trace_proj_of_isNormalized hq, hqw, hwq]
  rw [Matrix.proj_add]
  simp

theorem partialTrace_proj_add_kron_of_inner_eq_zero {n m : ℕ}
    (t p : Vector n) {w q : Vector m}
    (hw : Vector.IsNormalized w) (hq : Vector.IsNormalized q) (h : w† ⬝ q = 0) :
    partialTrace (n := n) (m := m) (Matrix.proj ((t ⊗ w) + (p ⊗ q))) =
      Matrix.proj t + Matrix.proj p := by
  have hqw : Matrix.trace (q ⬝ w†) = 0 := by
    rw [Matrix.trace_outer_eq_inner, h]
    simp
  have hwq_inner : q† ⬝ w = 0 := by
    have hadj := congrArg Matrix.adjoint h
    simpa using hadj
  have hwq : Matrix.trace (w ⬝ q†) = 0 := by
    rw [Matrix.trace_outer_eq_inner, hwq_inner]
    simp
  rw [Matrix.proj_add_kron, partialTrace_add_kron_four,
    Matrix.trace_proj_of_isNormalized hw, Matrix.trace_proj_of_isNormalized hq, hqw, hwq]
  simp

namespace Measurement

theorem partialProb_kron_of_isNormalized {n m : ℕ} (s : Vector n) {t : Vector m}
    (ht : Vector.IsNormalized t) :
    partialProb (s ⊗ t) = prob s := by
  funext i
  rw [partialProb, partialTrace_proj_kron_of_isNormalized (s := s) ht]
  simp [prob, Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, Complex.normSq]

theorem prob_eq_of_kron_eq {n m : ℕ} {a b : Vector n} {s t : Vector m}
    (h : a ⊗ s = b ⊗ t) (hs : Vector.IsNormalized s) (ht : Vector.IsNormalized t) :
    prob a = prob b := by
  have hpartial : partialProb (a ⊗ s) = partialProb (b ⊗ t) := by
    rw [h]
  rw [partialProb_kron_of_isNormalized a hs, partialProb_kron_of_isNormalized b ht] at hpartial
  exact hpartial

theorem partialProb_add_kron_apply_of_isNormalized {n m : ℕ}
    (a b : Vector n) {s t : Vector m}
    (hs : Vector.IsNormalized s) (ht : Vector.IsNormalized t) (i : Fin n) :
    partialProb ((a ⊗ s) + (b ⊗ t)) i =
      prob a i + (Matrix.trace (s ⬝ t†) * ((a ⬝ b†) i i)).re +
        (Matrix.trace (t ⬝ s†) * ((b ⬝ a†) i i)).re + prob b i := by
  have haDiag : ((Matrix.proj a) i i).re = prob a i := by
    simp [prob, Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
      Complex.normSq]
  have hbDiag : ((Matrix.proj b) i i).re = prob b i := by
    simp [prob, Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
      Complex.normSq]
  rw [partialProb, Matrix.proj_add_kron, partialTrace_add_kron_four,
    Matrix.trace_proj_of_isNormalized hs, Matrix.trace_proj_of_isNormalized ht]
  simp [haDiag, hbDiag]

theorem partialProb_add_kron_of_inner_eq_one {n m : ℕ}
    (a b : Vector n) {s t : Vector m}
    (hs : Vector.IsNormalized s) (ht : Vector.IsNormalized t) (h : s† ⬝ t = 1) :
    partialProb ((a ⊗ s) + (b ⊗ t)) = prob (a + b) := by
  funext i
  rw [partialProb, partialTrace_proj_add_kron_of_inner_eq_one a b hs ht h]
  simp [prob, Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, Complex.normSq]
  ring

theorem partialProb_add_kron_of_inner_eq_zero {n m : ℕ}
    (a b : Vector n) {s t : Vector m}
    (hs : Vector.IsNormalized s) (ht : Vector.IsNormalized t) (h : s† ⬝ t = 0) :
    partialProb ((a ⊗ s) + (b ⊗ t)) = fun i => prob a i + prob b i := by
  funext i
  rw [partialProb, partialTrace_proj_add_kron_of_inner_eq_zero a b hs ht h]
  simp [prob, Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply, Complex.normSq]

theorem partialProb_add_kron_of_pointwise_orthogonal {n m : ℕ}
    {a b : Vector n} {s t : Vector m}
    (hs : Vector.IsNormalized s) (ht : Vector.IsNormalized t)
    (h : ∀ i, star (a i 0) * b i 0 = 0) :
    partialProb ((a ⊗ s) + (b ⊗ t)) = prob (a + b) := by
  have hpartial :
      partialProb ((a ⊗ s) + (b ⊗ t)) = fun i => prob a i + prob b i := by
    funext i
    have hab : a i 0 * star (b i 0) = 0 := by
      have hstar := congrArg star (h i)
      simpa [map_mul, mul_comm] using hstar
    have hba : b i 0 * star (a i 0) = 0 := by
      simpa [mul_comm] using h i
    have habEntry : (a ⬝ b†) i i = 0 := by
      calc
        (a ⬝ b†) i i = a i 0 * star (b i 0) := by
          simp [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply]
        _ = 0 := hab
    have hbaEntry : (b ⬝ a†) i i = 0 := by
      calc
        (b ⬝ a†) i i = b i 0 * star (a i 0) := by
          simp [Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply]
        _ = 0 := hba
    have haDiag : ((Matrix.proj a) i i).re = prob a i := by
      simp [prob, Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
        Complex.normSq]
    have hbDiag : ((Matrix.proj b) i i).re = prob b i := by
      simp [prob, Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_apply,
        Complex.normSq]
    rw [partialProb, Matrix.proj_add_kron, partialTrace_add_kron_four,
      Matrix.trace_proj_of_isNormalized hs, Matrix.trace_proj_of_isNormalized ht]
    simp [habEntry, hbaEntry, haDiag, hbDiag]
  rw [hpartial, prob_add_of_pointwise_orthogonal h]

end Measurement

end Quantum
