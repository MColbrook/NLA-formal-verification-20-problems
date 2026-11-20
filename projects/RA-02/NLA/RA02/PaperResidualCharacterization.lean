module

public import NLA.RA02.PaperResidualZeros

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Matrix
namespace NLA.RA02.Paper

/-- Uniqueness of the approximation using the selected columns and interpolating the selected rows. -/
theorem residual_of_interpolating_coefficients {n s : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (rows cols : Fin s ↪ Fin n) (hu : IsUnit (A.submatrix rows cols))
    (Z : Matrix (Fin s) (Fin n) ℝ)
    (hZ : ∀ i : Fin s, ∀ j : Fin n, (A - A.submatrix id cols * Z) (rows i) j = 0) :
    A - A.submatrix id cols * Z = interpolatoryResidual A rows cols := by
  have he : A.submatrix rows cols * Z = A.submatrix rows id := by
    ext i j
    have hh := hZ i j
    exact (sub_eq_zero.mp hh).symm
  have hz : Z = (A.submatrix rows cols)⁻¹ * A.submatrix rows id := by
    rw [← he, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), Matrix.one_mul]
  rw [hz, ← Matrix.mul_assoc]
  rfl

#print axioms residual_of_interpolating_coefficients
end NLA.RA02.Paper
