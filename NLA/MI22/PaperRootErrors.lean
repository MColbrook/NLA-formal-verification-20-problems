module

public import NLA.MI22.PaperRootBounds

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace NLA.MI22.Paper

theorem eighth_root_factor_le :
    (1/8 : ℝ)*(1/1024 : ℝ)^((1/8 : ℝ)-1) ≤ 64 := by
  have hb : (1/1024 : ℝ) = (2 : ℝ)^(-10 : ℝ) := by norm_num [Real.rpow_neg]
  have he : (1/8 : ℝ)-1 = -7/8 := by norm_num
  rw [he,hb,← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hex : (-10 : ℝ)*(-7/8) = 35/4 := by norm_num
  rw [hex]
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : (35/4 : ℝ) ≤ 9)
  norm_num at h
  nlinarith

theorem eighth_root_error {n : ℕ} (Q R : Mat n) (hQ : Q.PosDef) (hR : R.PosDef)
    (hQfloor : (1/1024 : ℝ) • (1 : Mat n) ≤ Q)
    (hRfloor : (1/1024 : ℝ) • (1 : Mat n) ≤ R^(8 : ℕ))
    (hres : frobeniusSquared (R^(8 : ℕ)-Q) < (1/10000000000000000 : ℝ)) :
    operatorNorm (spectralPower Q (1/8)-R) < (64/100000000 : ℝ) := by
  have he : operatorNorm (Q-R^(8 : ℕ)) < (1/100000000 : ℝ) := by
    have hb := (euclidean_norm_bounds_proved (R^(8 : ℕ)-Q)).1
    have hh : operatorNorm (R^(8 : ℕ)-Q) < (1/100000000 : ℝ) := by nlinarith
    simpa only [operatorNorm_eq_l2, norm_sub_rev] using hh
  have h := root_lipschitz Q (R^(8 : ℕ)) (1/1024) (1/8)
    (by norm_num) (by norm_num) (by norm_num) hQ.isHermitian
    (naturalPower_posDef R hR 8).isHermitian hQfloor hRfloor
  rw [spectralPower_naturalPower R hR 8 (by norm_num)] at h
  norm_num only [Nat.cast_ofNat, show (8 : ℝ)*(1/8)=1 by norm_num] at h
  rw [spectralPower_one R hR] at h
  have hfactor := mul_le_mul_of_nonneg_right eighth_root_factor_le
    (operatorNorm_nonneg (Q-R^(8 : ℕ)))
  norm_num only at hfactor
  have hstrict := mul_lt_mul_of_pos_left he (by norm_num : (0 : ℝ) < 64)
  norm_num only [mul_one_div] at hstrict
  have hbound := h.trans hfactor
  linarith only [hbound, hstrict]

theorem paperX_error :
    operatorNorm (spectralPower paperC (1/8)-paperR) < (64/100000000 : ℝ) :=
  eighth_root_error _ _ paperC_posDef paperR_posDef
    (Matrix.le_iff.mpr paperC_floor_posDef.posSemidef) paperR_eighth_floor paperR_residual

theorem paperY_error :
    operatorNorm (spectralPower paperB (1/8)-paperS) < (64/100000000 : ℝ) :=
  eighth_root_error _ _ paperB_posDef paperS_posDef
    (Matrix.le_iff.mpr paperB_floor_posDef.posSemidef) paperS_eighth_floor paperS_residual

#print axioms paperX_error
#print axioms paperY_error
end NLA.MI22.Paper
