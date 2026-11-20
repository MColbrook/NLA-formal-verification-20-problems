module

public import NLA.MI21.GeneralMean.Positivity

@[expose] public section

set_option autoImplicit false
open Matrix
open scoped ComplexOrder MatrixOrder
noncomputable section
namespace NLA.MI21.GeneralMean

theorem height_cast (C D : Mat 2) (hC : C.PosDef) (hD : D.PosDef) :
    (height C D : ℂ) = (C⁻¹ * D).trace + 2 * (delta C D : ℂ) := by
  simp only [height, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [pos_cast_re (trace_inverse_mul_pos C D hC hD)]

theorem actual_scaled_riccati (C D : Mat 2) (hC : C.PosDef) (hD : D.PosDef) :
    numerator C D * C⁻¹ * numerator C D = (height C D : ℂ) • D := by
  have hdet := C.isUnit_iff_isUnit_det.mp hC.isUnit
  rw [height_cast C D hC hD]
  exact scaled_riccati_two_by_two C D C⁻¹ (delta C D : ℂ)
    (C.mul_nonsing_inv hdet) (C.nonsing_inv_mul hdet) (delta_squared C D hC hD)

theorem reciprocal_sqrt_squared (h : ℝ) (hh : 0 < h) :
    (((1 / Real.sqrt h : ℝ) : ℂ) * ((1 / Real.sqrt h : ℝ) : ℂ)) = ((1 / h : ℝ) : ℂ) := by
  have hs : (1 / Real.sqrt h) ^ 2 = 1 / h := by
    rw [_root_.one_div_pow, Real.sq_sqrt hh.le]
  exact_mod_cast (show (1 / Real.sqrt h) * (1 / Real.sqrt h) = 1 / h by
    simpa only [pow_two] using hs)

theorem actual_geometric_mean_two_by_two (C D : Mat 2) (hC : C.PosDef) (hD : D.PosDef) :
    geometricMean C D (1/2) = ((1 / Real.sqrt (height C D) : ℝ) : ℂ) • numerator C D := by
  let c : ℂ := ((1 / Real.sqrt (height C D) : ℝ) : ℂ)
  have hc : 0 ≤ c := by
    dsimp [c]
    exact_mod_cast (div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg (height C D)))
  have hc2 : c * c = ((1 / height C D : ℝ) : ℂ) :=
    reciprocal_sqrt_squared (height C D) (height_pos C D hC hD)
  have hX : (c • numerator C D).PosSemidef := (numerator_pos C D hC hD).smul hc
  have hXX : (c • numerator C D) * C⁻¹ * (c • numerator C D) = D := by
    calc
      (c • numerator C D) * C⁻¹ * (c • numerator C D) =
          (c * c) • (numerator C D * C⁻¹ * numerator C D) := by
        simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      _ = ((1 / height C D : ℝ) : ℂ) • ((height C D : ℂ) • D) := by
        rw [hc2, actual_scaled_riccati C D hC hD]
      _ = D := by
        rw [smul_smul]
        have hs : ((1 / height C D : ℝ) : ℂ) * (height C D : ℂ) = 1 := by
          exact_mod_cast (one_div_mul_cancel (height_pos C D hC hD).ne')
        rw [hs, one_smul]
  exact geometricMean_eq_of_riccati C D C⁻¹ (c • numerator C D) hC hX
    (C.mul_nonsing_inv (C.isUnit_iff_isUnit_det.mp hC.isUnit)) hXX

theorem actual_geometric_mean_squared_two_by_two (C D : Mat 2)
    (hC : C.PosDef) (hD : D.PosDef) :
    geometricMean C D (1/2) ^ (2 : ℕ) = ((1 / height C D : ℝ) : ℂ) • numerator C D ^ (2 : ℕ) := by
  rw [actual_geometric_mean_two_by_two C D hC hD]
  simp only [pow_two, smul_mul_assoc, mul_smul_comm, smul_smul,
    reciprocal_sqrt_squared (height C D) (height_pos C D hC hD)]

#print axioms height_cast
#print axioms actual_scaled_riccati
#print axioms reciprocal_sqrt_squared
#print axioms actual_geometric_mean_two_by_two
#print axioms actual_geometric_mean_squared_two_by_two
end NLA.MI21.GeneralMean
