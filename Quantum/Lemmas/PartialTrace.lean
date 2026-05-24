import Quantum.State
import Quantum.Lemmas.Gates

namespace Quantum

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

@[simp]
theorem partialTrace_kron_proj_of_isUnit {n m : ℕ} (A : Square n) {s : Vector m}
    (hs : Matrix.isUnit s) :
    partialTrace (n := n) (m := m) (A ⊗ Matrix.proj s) = A := by
  rw [partialTrace_kron, Matrix.trace_proj_of_isUnit hs]
  simp

@[simp]
theorem partialTrace_proj_kron_of_isUnit {n m : ℕ} (s : Vector n) {t : Vector m}
    (ht : Matrix.isUnit t) :
    partialTrace (n := n) (m := m) (Matrix.proj (s ⊗ t)) = Matrix.proj s := by
  rw [Matrix.proj_kron]
  exact partialTrace_kron_proj_of_isUnit (Matrix.proj s) ht

theorem partialTrace_proj_eq_of_kron_eq {n m : ℕ} {a b : Vector n} {s t : Vector m}
    (h : a ⊗ s = b ⊗ t) (hs : Matrix.isUnit s) (ht : Matrix.isUnit t) :
    Matrix.proj a = Matrix.proj b := by
  have hpartial :
      partialTrace (n := n) (m := m) (Matrix.proj (a ⊗ s)) =
        partialTrace (n := n) (m := m) (Matrix.proj (b ⊗ t)) := by
    rw [h]
  rw [partialTrace_proj_kron_of_isUnit (s := a) hs] at hpartial
  rw [partialTrace_proj_kron_of_isUnit (s := b) ht] at hpartial
  exact hpartial

@[simp]
theorem partialTrace_proj_ket00 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket00) = P0 := by
  rw [← ket0_kron_ket0]
  rw [← proj_ket0]
  exact partialTrace_proj_kron_of_isUnit (s := ket0) ket0_isUnit

@[simp]
theorem partialTrace_proj_ket01 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket01) = P0 := by
  rw [← ket0_kron_ket1]
  rw [← proj_ket0]
  exact partialTrace_proj_kron_of_isUnit (s := ket0) ket1_isUnit

@[simp]
theorem partialTrace_proj_ket10 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket10) = P1 := by
  rw [← ket1_kron_ket0]
  rw [← proj_ket1]
  exact partialTrace_proj_kron_of_isUnit (s := ket1) ket0_isUnit

@[simp]
theorem partialTrace_proj_ket11 :
    partialTrace (n := 2) (m := 2) (Matrix.proj ket11) = P1 := by
  rw [← ket1_kron_ket1]
  rw [← proj_ket1]
  exact partialTrace_proj_kron_of_isUnit (s := ket1) ket1_isUnit

@[simp]
theorem partialTrace_proj_ketPhiPlus :
    partialTrace (n := 2) (m := 2) (Matrix.proj ketPhiPlus) = ((1 / 2 : ℂ) • (I 2)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partialTrace, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPhiPlus,
      _root_.Matrix.mul_apply, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.sum_univ_two]

@[simp]
theorem partialTrace_pure_ket00 :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ket00) = P0 := by
  simp [DensityMatrix.pure]

@[simp]
theorem partialTrace_pure_ket01 :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ket01) = P0 := by
  simp [DensityMatrix.pure]

@[simp]
theorem partialTrace_pure_ket10 :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ket10) = P1 := by
  simp [DensityMatrix.pure]

@[simp]
theorem partialTrace_pure_ket11 :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ket11) = P1 := by
  simp [DensityMatrix.pure]

@[simp]
theorem partialTrace_pure_ketPhiPlus :
    partialTrace (n := 2) (m := 2) (DensityMatrix.pure ketPhiPlus) = ((1 / 2 : ℂ) • (I 2)) := by
  simp [DensityMatrix.pure]

end Quantum
