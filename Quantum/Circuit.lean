import Quantum.Circuit.Register

/-!
# Quantum Circuits

Typed circuit syntax, denotational semantics, execution on registers, and
unitary circuit composition.
-/

namespace Quantum

/-- Typed quantum circuits indexed by qubit count. -/
inductive Circuit : ℕ → Type where
  | id (n : ℕ) : Circuit n
  | gate {n : ℕ} (U : Circuit.Register.Gate n) : Circuit n
  | seq {n : ℕ} (first second : Circuit n) : Circuit n
  | tensor {n m : ℕ} (left : Circuit n) (right : Circuit m) : Circuit (n + m)

namespace Circuit

/-- Denotational semantics of a circuit as a register gate. -/
noncomputable def denote : {n : ℕ} → Circuit n → Register.Gate n
  | n, id _ => I (Register.dimension n)
  | _, gate U => U
  | _, seq first second => denote second ⬝ denote first
  | _, tensor left right => Register.tensorGate (denote left) (denote right)

/-- Run a circuit on a register state vector. -/
noncomputable def run {n : ℕ} (c : Circuit n) (s : Register.State n) : Register.State n :=
  c.denote ⬝ s

/-- A circuit is unitary when its denotation is a unitary matrix. -/
def IsUnitary {n : ℕ} (c : Circuit n) : Prop :=
  Matrix.isUnitary c.denote

/-- Circuits carrying a proof that their denotation is unitary. -/
structure Unitary (n : ℕ) where
  circuit : Circuit n
  isUnitary : circuit.IsUnitary

namespace Unitary

variable {n m : ℕ}

instance : Coe (Unitary n) (Circuit n) where
  coe c := c.circuit

/-- The identity unitary circuit. -/
noncomputable def id (n : ℕ) : Unitary n where
  circuit := Circuit.id n
  isUnitary := by
    simp [Circuit.IsUnitary, Circuit.denote]

/-- Promote a gate with a unitary proof to a unitary circuit. -/
noncomputable def gate (U : Register.Gate n) (hU : Matrix.isUnitary U) : Unitary n where
  circuit := Circuit.gate U
  isUnitary := by
    simpa [Circuit.IsUnitary, Circuit.denote] using hU

/-- Sequentially compose unitary circuits. `seq first second` applies `first`, then `second`. -/
noncomputable def seq (first second : Unitary n) : Unitary n where
  circuit := Circuit.seq first.circuit second.circuit
  isUnitary := by
    exact Matrix.isUnitary_mul second.isUnitary first.isUnitary

/-- Tensor unitary circuits into a circuit on the combined register. -/
noncomputable def tensor (left : Unitary n) (right : Unitary m) : Unitary (n + m) where
  circuit := Circuit.tensor left.circuit right.circuit
  isUnitary := by
    exact Register.isUnitary_tensorGate left.isUnitary right.isUnitary

/-- Denotational semantics of a unitary circuit. -/
noncomputable def denote (c : Unitary n) : Register.Gate n :=
  c.circuit.denote

/-- Run a unitary circuit on a register state vector. -/
noncomputable def run (c : Unitary n) (s : Register.State n) : Register.State n :=
  c.denote ⬝ s

theorem run_isNormalized (c : Unitary n) {s : Register.State n} (hs : Vector.IsNormalized s) :
    Vector.IsNormalized (c.run s) :=
  Matrix.isUnitary_mul_isNormalized c.isUnitary hs

end Unitary

end Circuit

end Quantum
