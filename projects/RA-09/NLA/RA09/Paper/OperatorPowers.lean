module

public import NLA.RA09.Paper.Powers
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order

@[expose] public section

/-! Operator monotonicity of the sharpness powers, for matrices of every size.
Mathlib's proof uses the positive integral representation of the power function. -/
set_option autoImplicit false
noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
namespace NLA.RA09.Paper

theorem power_operator_monotone {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {n : ℕ} {X Y : Matrix (Fin n) (Fin n) ℂ}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hXY : X ≤ Y) :
    cfc (fun x : ℝ => x ^ p) X ≤ cfc (fun x : ℝ => x ^ p) Y := by
  rw [← CFC.rpow_eq_cfc_real hX.nonneg, ← CFC.rpow_eq_cfc_real hY.nonneg]
  exact CFC.rpow_le_rpow ⟨hp, hp1⟩ hXY

#print axioms power_operator_monotone

end NLA.RA09.Paper
