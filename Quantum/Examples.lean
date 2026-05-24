import Quantum.Circuit
import Quantum.Gates

namespace Quantum

namespace Circuit

namespace Unitary

/-- The Pauli-X gate as a one-qubit unitary circuit. -/
noncomputable def x : Unitary 1 :=
  gate X X_isUnitary

/-- The Pauli-Z gate as a one-qubit unitary circuit. -/
noncomputable def z : Unitary 1 :=
  gate Z Z_isUnitary

/-- The Hadamard gate as a one-qubit unitary circuit. -/
noncomputable def h : Unitary 1 :=
  gate H H_isUnitary

/-- The CNOT gate as a two-qubit unitary circuit. -/
noncomputable def cnot : Unitary 2 :=
  gate CNOT CNOT_isUnitary

/-- The controlled-Z gate as a two-qubit unitary circuit. -/
noncomputable def cz : Unitary 2 :=
  gate CZ CZ_isUnitary

/-- The two-qubit swap gate as a unitary circuit. -/
noncomputable def swap : Unitary 2 :=
  gate SWAP SWAP_isUnitary

/-- Apply Hadamard to the first qubit of a two-qubit register. -/
noncomputable def hadamardOnFirst : Unitary 2 :=
  tensor h (id 1)

/-- Bell-state preparation circuit: apply `H` to the first qubit, then `CNOT`. -/
noncomputable def bell : Unitary 2 :=
  seq hadamardOnFirst cnot

@[simp]
theorem denote_x : x.denote = X :=
  rfl

@[simp]
theorem denote_z : z.denote = Z :=
  rfl

@[simp]
theorem denote_h : h.denote = H :=
  rfl

@[simp]
theorem denote_cnot : cnot.denote = CNOT :=
  rfl

@[simp]
theorem denote_cz : cz.denote = CZ :=
  rfl

@[simp]
theorem denote_swap : swap.denote = SWAP :=
  rfl

@[simp]
theorem denote_hadamardOnFirst : hadamardOnFirst.denote = H ⊗ (I 2) := by
  change Register.tensorGate h.denote ((id 1).denote) = H ⊗ (I 2)
  rw [denote_h]
  change Register.tensorGate (n := 1) (m := 1) H (I 2) = H ⊗ (I 2)
  change (Matrix.reindex (Equiv.refl (Fin 4)) (Equiv.refl (Fin 4))) (H ⊗ (I 2)) =
    H ⊗ (I 2)
  exact _root_.Matrix.reindex_refl_refl (H ⊗ (I 2))

@[simp]
theorem denote_bell : bell.denote = CNOT ⬝ (H ⊗ (I 2)) := by
  change cnot.denote ⬝ hadamardOnFirst.denote = CNOT ⬝ (H ⊗ (I 2))
  rw [denote_cnot, denote_hadamardOnFirst]
  rfl

@[simp]
theorem run_bell_ket00 : bell.run ket00 = ketPhiPlus := by
  change bell.denote ⬝ ket00 = ketPhiPlus
  rw [denote_bell]
  change (CNOT * (H ⊗ (I 2))) * ket00 = ketPhiPlus
  rw [_root_.Matrix.mul_assoc]
  exact bell_state_preparation

end Unitary

end Circuit

end Quantum
