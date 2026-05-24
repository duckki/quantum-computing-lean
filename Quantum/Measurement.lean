import Quantum.State

namespace Quantum

namespace Measurement

/-- A family of measurement operators is complete when the effects sum to identity. -/
def IsComplete {n outcomes : ℕ} (M : Fin outcomes → Square n) : Prop :=
  (∑ m : Fin outcomes, (M m)† ⬝ M m) = I n

/-- Generalized measurement operators satisfying the completeness condition. -/
structure Generalized (n outcomes : ℕ) where
  operator : Fin outcomes → Square n
  isComplete : IsComplete operator

namespace Generalized

variable {n outcomes : ℕ}

instance : CoeFun (Generalized n outcomes) (fun _ => Fin outcomes → Square n) where
  coe M := M.operator

@[simp]
theorem coe_apply (M : Generalized n outcomes) (m : Fin outcomes) :
    (M : Fin outcomes → Square n) m = M.operator m :=
  rfl

/-- Probability of generalized measurement outcome `m`. -/
noncomputable def prob (M : Generalized n outcomes) (s : Vector n) (m : Fin outcomes) : ℝ :=
  generalizedProb M.operator s m

/-- Normalized post-measurement state after generalized measurement outcome `m`. -/
noncomputable def postMeasure
    (M : Generalized n outcomes) (s : Vector n) (m : Fin outcomes) : Vector n :=
  generalizedPostMeasure M.operator s m

/-- Probability of outcome `m` for a pure state. -/
noncomputable def pureProb (M : Generalized n outcomes) (ψ : PureState n)
    (m : Fin outcomes) : ℝ :=
  M.prob ψ.vector m

/-- Post-measurement vector after measuring a pure state. -/
noncomputable def purePostMeasure (M : Generalized n outcomes) (ψ : PureState n)
    (m : Fin outcomes) : Vector n :=
  M.postMeasure ψ.vector m

end Generalized

end Measurement

end Quantum
