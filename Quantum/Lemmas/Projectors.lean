import Quantum.Lemmas.States

namespace Quantum

@[simp]
theorem P0_mul_ket0 : P0 ⬝ ket0 = ket0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P0, ket0, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P0_mul_ket1 : P0 ⬝ ket1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P0, ket1, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P1_mul_ket0 : P1 ⬝ ket0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P1, ket0, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P1_mul_ket1 : P1 ⬝ ket1 = ket1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P1, ket1, Vector.basis, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P0_adjoint : P0† = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, P0]

@[simp]
theorem P1_adjoint : P1† = P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.adjoint, P1]

@[simp]
theorem P0_mul_self : P0 ⬝ P0 = P0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P0, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P1_mul_self : P1 ⬝ P1 = P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P1, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P0_mul_P1 : P0 ⬝ P1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P0, P1, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem P1_mul_P0 : P1 ⬝ P0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul, P0, P1, _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem trace_P0 : Tr(P0) = 1 := by
  simpa [proj_ket0] using Matrix.trace_proj_of_isUnit ket0_isUnit

@[simp]
theorem trace_P1 : Tr(P1) = 1 := by
  simpa [proj_ket1] using Matrix.trace_proj_of_isUnit ket1_isUnit

@[simp]
theorem P0_add_P1 : P0 + P1 = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [P0, P1]

@[simp]
theorem PPlus_mul_ketPlus : PPlus ⬝ ketPlus = ketPlus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, _root_.Matrix.mul_apply]

@[simp]
theorem PPlus_mul_ketMinus : PPlus ⬝ ketMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply]

@[simp]
theorem PMinus_mul_ketPlus : PMinus ⬝ ketPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply]

@[simp]
theorem PMinus_mul_ketMinus : PMinus ⬝ ketMinus = ketMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketMinus, _root_.Matrix.mul_apply] <;>
    ring_nf

@[simp]
theorem PPlus_adjoint : PPlus† = PPlus := by
  simp [PPlus]

@[simp]
theorem PMinus_adjoint : PMinus† = PMinus := by
  simp [PMinus]

@[simp]
theorem PPlus_mul_self : PPlus ⬝ PPlus = PPlus := by
  simpa [PPlus] using Matrix.proj_mul_proj_of_isUnit ketPlus_isUnit

@[simp]
theorem PMinus_mul_self : PMinus ⬝ PMinus = PMinus := by
  simpa [PMinus] using Matrix.proj_mul_proj_of_isUnit ketMinus_isUnit

@[simp]
theorem trace_PPlus : Tr(PPlus) = 1 := by
  simpa [PPlus] using Matrix.trace_proj_of_isUnit ketPlus_isUnit

@[simp]
theorem trace_PMinus : Tr(PMinus) = 1 := by
  simpa [PMinus] using Matrix.trace_proj_of_isUnit ketMinus_isUnit

@[simp]
theorem PPlus_mul_PMinus : PPlus ⬝ PMinus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem PMinus_mul_PPlus : PMinus ⬝ PPlus = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply, Fin.sum_univ_two]

@[simp]
theorem PPlus_add_PMinus : PPlus + PMinus = I 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [PPlus, PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply] <;>
    ring_nf

theorem I_eq_add_P0_P1 : (I 2) = P0 + P1 := by
  rw [P0_add_P1]

theorem I_eq_add_PPlus_PMinus : (I 2) = PPlus + PMinus := by
  rw [PPlus_add_PMinus]

theorem X_eq_sub_PPlus_PMinus : X = PPlus - PMinus := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X, PPlus, PMinus, Matrix.proj, Matrix.mul, Matrix.adjoint, ketPlus, ketMinus,
      _root_.Matrix.mul_apply] <;>
    ring_nf

theorem Z_eq_sub_P0_P1 : Z = P0 - P1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Z, P0, P1]

end Quantum
