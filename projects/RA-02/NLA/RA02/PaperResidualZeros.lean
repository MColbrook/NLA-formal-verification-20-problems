module

public import NLA.RA02.PaperResidualBorder

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace NLA.RA02.Paper

theorem residual_selected_row {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin s ↪ Fin n) (hu : IsUnit (A.submatrix rows cols)) (i : Fin s) (j : Fin n) :
    interpolatoryResidual A rows cols (rows i) j = 0 := by
  have hh : (A.submatrix id cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id).submatrix rows id =
      A.submatrix rows cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id := by
    rfl
  rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mul] at hh
  have he := congrFun (congrFun hh i) j
  exact sub_eq_zero.mpr he.symm

theorem residual_selected_column {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin s ↪ Fin n) (hu : IsUnit (A.submatrix rows cols)) (i : Fin n) (j : Fin s) :
    interpolatoryResidual A rows cols i (cols j) = 0 := by
  have hh : (A.submatrix id cols * (A.submatrix rows cols)⁻¹ * A.submatrix rows id).submatrix id cols =
      A.submatrix id cols * ((A.submatrix rows cols)⁻¹ * A.submatrix rows cols) := by
    rw [Matrix.mul_assoc]
    rfl
  rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.mul_one] at hh
  have he := congrFun (congrFun hh i) j
  exact sub_eq_zero.mpr he.symm

#print axioms residual_selected_row
end NLA.RA02.Paper
