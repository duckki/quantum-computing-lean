import Mathlib.Analysis.Matrix.PosDef
import Quantum.Basic
import Quantum.Lemmas.Core

namespace Quantum

open scoped ComplexOrder

/-- A density matrix is represented as a square complex matrix. -/
abbrev DensityMatrix (n : ℕ) := Square n

namespace DensityMatrix

variable {n : ℕ}

/-- A density matrix is Hermitian when it is equal to its adjoint. -/
def isHermitian (ρ : DensityMatrix n) : Prop :=
  ρ† = ρ

/-- Positive semidefiniteness, using mathlib's matrix predicate. -/
def isPositive (ρ : DensityMatrix n) : Prop :=
  _root_.Matrix.PosSemidef ρ

/-- A density matrix has trace one when its trace is exactly `1`. -/
def hasTraceOne (ρ : DensityMatrix n) : Prop :=
  Tr(ρ) = 1

/-- The density-matrix well-formedness predicate. -/
def isDensity (ρ : DensityMatrix n) : Prop :=
  isPositive ρ ∧ hasTraceOne ρ

/-- The density matrix associated to a pure state vector. -/
noncomputable def pure (s : Vector n) : DensityMatrix n :=
  Matrix.proj s

/-- Unitary evolution of a density matrix: `ρ ↦ UρU†`. -/
noncomputable def evolve (U : Square n) (ρ : DensityMatrix n) : DensityMatrix n :=
  U ⬝ ρ ⬝ U†

@[simp]
theorem pure_eq_proj (s : Vector n) : pure s = Matrix.proj s :=
  rfl

@[simp]
theorem pure_isHermitian (s : Vector n) : isHermitian (pure s) := by
  simp [isHermitian, pure]

theorem pure_isPositive (s : Vector n) : isPositive (pure s) := by
  simpa [isPositive, pure, Matrix.proj, Matrix.mul, Matrix.adjoint] using
    _root_.Matrix.posSemidef_self_mul_conjTranspose (A := s)

theorem trace_pure_of_isUnit {s : Vector n} (hs : Matrix.isUnit s) :
    Tr(pure s) = 1 := by
  simpa [pure] using Matrix.trace_proj_of_isUnit hs

theorem pure_hasTraceOne_of_isUnit {s : Vector n} (hs : Matrix.isUnit s) :
    hasTraceOne (pure s) := by
  exact trace_pure_of_isUnit hs

theorem pure_isDensity_of_isUnit {s : Vector n} (hs : Matrix.isUnit s) :
    isDensity (pure s) := by
  exact ⟨pure_isPositive s, pure_hasTraceOne_of_isUnit hs⟩

@[simp]
theorem evolve_apply (U : Square n) (ρ : DensityMatrix n) :
    evolve U ρ = U ⬝ ρ ⬝ U† :=
  rfl

theorem evolve_pure (U : Square n) (s : Vector n) :
    evolve U (pure s) = pure (U ⬝ s) := by
  simp [evolve, pure, Matrix.proj, Matrix.mul, Matrix.adjoint, _root_.Matrix.mul_assoc]

end DensityMatrix

/-- A pure state is a normalized state vector. -/
structure PureState (n : ℕ) where
  vector : Vector n
  isUnit : Matrix.isUnit vector

namespace PureState

variable {n : ℕ}

instance : Coe (PureState n) (Vector n) where
  coe ψ := ψ.vector

@[simp]
theorem coe_mk (s : Vector n) (hs : Matrix.isUnit s) :
    ((PureState.mk s hs : PureState n) : Vector n) = s :=
  rfl

/-- The density matrix associated to a pure state. -/
noncomputable def density (ψ : PureState n) : DensityMatrix n :=
  DensityMatrix.pure ψ.vector

theorem density_isDensity (ψ : PureState n) :
    DensityMatrix.isDensity ψ.density :=
  DensityMatrix.pure_isDensity_of_isUnit ψ.isUnit

/-- Evolve a pure state by a unitary gate. -/
noncomputable def evolve (U : Square n) (hU : Matrix.isUnitary U) (ψ : PureState n) :
    PureState n where
  vector := U ⬝ ψ.vector
  isUnit := Matrix.isUnitary_mul_isUnit hU ψ.isUnit

@[simp]
theorem evolve_vector (U : Square n) (hU : Matrix.isUnitary U) (ψ : PureState n) :
    (evolve U hU ψ).vector = U ⬝ ψ.vector :=
  rfl

@[simp]
theorem density_evolve (U : Square n) (hU : Matrix.isUnitary U) (ψ : PureState n) :
    (evolve U hU ψ).density = DensityMatrix.evolve U ψ.density := by
  simpa [density] using (DensityMatrix.evolve_pure U ψ.vector).symm

end PureState

end Quantum
