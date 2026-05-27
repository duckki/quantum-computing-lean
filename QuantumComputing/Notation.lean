import QuantumComputing.Gates

/-!
# Scoped Quantum Notation

Opt-in Dirac ket notation and common gate aliases.

Use `open scoped QuantumComputing` after importing this module, or after importing
the top-level `QuantumComputing` module.
-/

namespace QuantumComputing

scoped[QuantumComputing] notation "|0⟩" => ket0
scoped[QuantumComputing] notation "|1⟩" => ket1

scoped[QuantumComputing] notation "|00⟩" => ket00
scoped[QuantumComputing] notation "|01⟩" => ket01
scoped[QuantumComputing] notation "|10⟩" => ket10
scoped[QuantumComputing] notation "|11⟩" => ket11

scoped[QuantumComputing] notation "|0^" n "⟩" => ketZeros n
scoped[QuantumComputing] notation "|0^(" n ")⟩" => ketZeros n

scoped[QuantumComputing] notation "|+⟩" => ketPlus
scoped[QuantumComputing] notation "|-⟩" => ketMinus
scoped[QuantumComputing] notation "|Φ+⟩" => ketPhiPlus

/-- Common controlled-X alias for `CNOT`. -/
abbrev CX : Square 4 := CNOT

/-- Common controlled-controlled-X alias for the Toffoli gate. -/
abbrev CCX : Square 8 := TOFFOLI

/-- Common controlled-controlled-NOT alias for the Toffoli gate. -/
abbrev CCNOT : Square 8 := TOFFOLI

end QuantumComputing

open scoped QuantumComputing

example : |0⟩ = QuantumComputing.ket0 := rfl
example : |1⟩ = QuantumComputing.ket1 := rfl
example : |+⟩ = QuantumComputing.ketPlus := rfl
example : |-⟩ = QuantumComputing.ketMinus := rfl
example : |Φ+⟩ = QuantumComputing.ketPhiPlus := rfl
example (n : ℕ) : |0^n⟩ = QuantumComputing.ketZeros n := rfl
example (n : ℕ) : |0^(n)⟩ = QuantumComputing.ketZeros n := rfl
