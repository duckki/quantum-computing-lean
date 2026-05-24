import Mathlib.Analysis.SpecialFunctions.Sqrt
import Quantum.Matrix

namespace Quantum

noncomputable def invSqrt2 : ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ)

def ket0 : Vector 2 := Vector.basis 0
def ket1 : Vector 2 := Vector.basis 1

def ket00 : Vector 4 := Vector.basis 0
def ket01 : Vector 4 := Vector.basis 1
def ket10 : Vector 4 := Vector.basis 2
def ket11 : Vector 4 := Vector.basis 3

def ketZeros (n : ℕ) : Vector (2 ^ n) :=
  Vector.basis ⟨0, by simp⟩

noncomputable def ketPlus : Vector 2 :=
  fun i _ => if (i : ℕ) = 0 then invSqrt2 else invSqrt2

noncomputable def ketMinus : Vector 2 :=
  fun i _ => if (i : ℕ) = 0 then invSqrt2 else -invSqrt2

noncomputable def ketPhiPlus : Vector 4 :=
  fun i _ =>
    if (i : ℕ) = 0 then invSqrt2
    else if (i : ℕ) = 3 then invSqrt2
    else 0

def X : Square 2 :=
  fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then 1
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then 1
    else 0

def Z : Square 2 :=
  fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 1
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 1 then -1
    else 0

noncomputable def H : Square 2 :=
  fun i j =>
    if (i : ℕ) = 1 ∧ (j : ℕ) = 1 then -invSqrt2
    else invSqrt2

def CNOT : Square 4 :=
  fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 1
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 1 then 1
    else if (i : ℕ) = 2 ∧ (j : ℕ) = 3 then 1
    else if (i : ℕ) = 3 ∧ (j : ℕ) = 2 then 1
    else 0

def CZ : Square 4 :=
  fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 1
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 1 then 1
    else if (i : ℕ) = 2 ∧ (j : ℕ) = 2 then 1
    else if (i : ℕ) = 3 ∧ (j : ℕ) = 3 then -1
    else 0

def SWAP : Square 4 :=
  fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 1
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 2 then 1
    else if (i : ℕ) = 2 ∧ (j : ℕ) = 1 then 1
    else if (i : ℕ) = 3 ∧ (j : ℕ) = 3 then 1
    else 0

def P0 : Square 2 :=
  fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 1 else 0

def P1 : Square 2 :=
  fun i j =>
    if (i : ℕ) = 1 ∧ (j : ℕ) = 1 then 1 else 0

noncomputable def PPlus : Square 2 :=
  Matrix.proj ketPlus

noncomputable def PMinus : Square 2 :=
  Matrix.proj ketMinus

noncomputable def controlledGate {n : ℕ} (U : Square n) : Square (2 * n) :=
  Matrix.proj ket0 ⊗ (I n) + Matrix.proj ket1 ⊗ U

noncomputable def gateControlled (U : Square 2) : Square 4 :=
  SWAP ⬝ controlledGate U ⬝ SWAP

noncomputable def partialTrace {n m : ℕ} (A : Square (n * m)) : Square n :=
  fun i j => ∑ k : Fin m, A (finProdFinEquiv (i, k)) (finProdFinEquiv (j, k))

namespace Measurement

/-- Probability of observing computational-basis outcome `i` when measuring `s`. -/
def prob {n : ℕ} (s : Vector n) (i : Fin n) : ℝ :=
  Complex.normSq (s i 0)

/-- Normalized post-measurement state after observing computational-basis outcome `i`. -/
noncomputable def postMeasure {n : ℕ} (s : Vector n) (i : Fin n) : Vector n :=
  ((1 / Real.sqrt (prob s i) : ℝ) : ℂ) • (Matrix.proj (Vector.basis i) ⬝ s)

noncomputable def generalizedProb {n outcomes : ℕ}
    (M : Fin outcomes → Square n) (s : Vector n) (m : Fin outcomes) : ℝ :=
  ((s† ⬝ ((M m)† ⬝ M m) ⬝ s) 0 0).re

noncomputable def generalizedPostMeasure {n outcomes : ℕ}
    (M : Fin outcomes → Square n) (s : Vector n) (m : Fin outcomes) : Vector n :=
  ((1 / Real.sqrt (generalizedProb M s m) : ℝ) : ℂ) • (M m ⬝ s)

end Measurement

end Quantum
