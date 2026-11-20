module

public import NLA.MI21.GeneralMean.Definitions
public import NLA.MI21.GeneralMean.CayleyHamilton

@[expose] public section

set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI21.GeneralMean

theorem pos_cast_re {z : ℂ} (hz : 0 < z) : (z.re : ℂ) = z := by
  apply Complex.ext
  · rfl
  · exact (Complex.pos_iff.mp hz).2

theorem determinant_ratio_pos (C D : Mat 2) (hC : C.PosDef) (hD : D.PosDef) :
    0 < D.det / C.det := div_pos hD.det_pos hC.det_pos

theorem delta_pos (C D : Mat 2) (hC : C.PosDef) (hD : D.PosDef) :
    0 < delta C D := by
  exact Real.sqrt_pos.mpr (Complex.pos_iff.mp (determinant_ratio_pos C D hC hD)).1

theorem delta_squared (C D : Mat 2) (hC : C.PosDef) (hD : D.PosDef) :
    (delta C D : ℂ) ^ 2 = (C⁻¹ * D).det := by
  have hs : delta C D ^ 2 = (D.det / C.det).re :=
    Real.sq_sqrt (Complex.pos_iff.mp (determinant_ratio_pos C D hC hD)).1.le
  calc
    (delta C D : ℂ) ^ 2 = ((D.det / C.det).re : ℂ) := by exact_mod_cast hs
    _ = D.det / C.det := pos_cast_re (determinant_ratio_pos C D hC hD)
    _ = (C⁻¹ * D).det := by
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      ring

theorem trace_inverse_mul_pos (C D : Mat 2) (hC : C.PosDef) (hD : D.PosDef) :
    0 < (C⁻¹ * D).trace := by
  let H := CFC.rpow C⁻¹ (1/2)
  have hH : H.PosDef := spectralPower_posDef C⁻¹ hC.inv (1/2)
  have hHH : H * H = C⁻¹ := by
    dsimp [H]
    rw [← CFC.rpow_add hC.inv.isUnit]
    norm_num
    exact CFC.rpow_one C⁻¹ hC.inv.posSemidef.nonneg
  have hZ : (H * D * H).PosDef := by
    simpa only [hH.isHermitian.eq] using
      hD.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hH.isUnit)
  have ht : (H * D * H).trace = (C⁻¹ * D).trace := by
    rw [Matrix.trace_mul_cycle, hHH]
  rw [← ht]
  exact hZ.trace_pos

theorem height_pos (C D : Mat 2) (hC : C.PosDef) (hD : D.PosDef) :
    0 < height C D := by
  exact add_pos (Complex.pos_iff.mp (trace_inverse_mul_pos C D hC hD)).1
    (mul_pos (by norm_num) (delta_pos C D hC hD))

theorem numerator_pos (C D : Mat 2) (hC : C.PosDef) (hD : D.PosDef) :
    (numerator C D).PosSemidef := by
  apply hD.posSemidef.add
  exact hC.posSemidef.smul (by exact_mod_cast (delta_pos C D hC hD).le)

#print axioms pos_cast_re
#print axioms determinant_ratio_pos
#print axioms delta_pos
#print axioms delta_squared
#print axioms trace_inverse_mul_pos
#print axioms height_pos
#print axioms numerator_pos
end NLA.MI21.GeneralMean
