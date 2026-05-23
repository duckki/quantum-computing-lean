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

def measure {n : ℕ} (s : Vector n) (i : Fin n) : ℝ :=
  Complex.normSq (s i 0)

noncomputable def stateAfterMeasure {n : ℕ} (s : Vector n) (i : Fin n) : Vector n :=
  ((1 / Real.sqrt (measure s i) : ℝ) : ℂ) • (Matrix.proj (Vector.basis i) ⬝ s)

noncomputable def genMeasure {n : ℕ} (M : Fin n → Square n) (s : Vector n) (m : Fin n) : ℝ :=
  ((s† ⬝ ((M m)† ⬝ M m) ⬝ s) 0 0).re

noncomputable def stateAfterGenMeasure {n : ℕ} (M : Fin n → Square n)
    (s : Vector n) (m : Fin n) : Vector n :=
  ((1 / Real.sqrt (genMeasure M s m) : ℝ) : ℂ) • (M m ⬝ s)

end Quantum
