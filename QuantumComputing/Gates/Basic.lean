import QuantumComputing.States

/-!
# Basic Gates

Concrete one- and two-qubit gate matrices and basic controlled-gate
constructors.
-/

namespace QuantumComputing

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

/-- Three-qubit Toffoli gate, flipping the last qubit when the first two are `1`. -/
def TOFFOLI : Square 8 :=
  fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then 1
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 1 then 1
    else if (i : ℕ) = 2 ∧ (j : ℕ) = 2 then 1
    else if (i : ℕ) = 3 ∧ (j : ℕ) = 3 then 1
    else if (i : ℕ) = 4 ∧ (j : ℕ) = 4 then 1
    else if (i : ℕ) = 5 ∧ (j : ℕ) = 5 then 1
    else if (i : ℕ) = 6 ∧ (j : ℕ) = 7 then 1
    else if (i : ℕ) = 7 ∧ (j : ℕ) = 6 then 1
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

noncomputable def controlledGate {n : ℕ} (U : Square n) : Square (2 * n) :=
  Matrix.proj ket0 ⊗ (I n) + Matrix.proj ket1 ⊗ U

noncomputable def gateControlled (U : Square 2) : Square 4 :=
  SWAP ⬝ controlledGate U ⬝ SWAP

end QuantumComputing
