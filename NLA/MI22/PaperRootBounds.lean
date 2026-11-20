module

public import NLA.MI22.PaperRootLipschitz
public import NLA.MI22.PaperPositivity
public import NLA.MI22.PaperNumeric

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace NLA.MI22.Paper

theorem posDef_of_positive_lower {n : ℕ} (Q : Mat n) (c : ℝ) (hc : 0 ≤ c)
    (hQ : (Q-c • (1 : Mat n)).PosDef) : Q.PosDef := by
  have hi : (c • (1 : Mat n)).PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (smul_nonneg hc (show (0 : Mat n) ≤ 1 from zero_le_one))
  simpa only [sub_add_cancel] using hQ.add_posSemidef hi

theorem paperB_posDef : paperB.PosDef :=
  posDef_of_positive_lower _ _ (by norm_num) paperB_floor_posDef
theorem paperC_posDef : paperC.PosDef :=
  posDef_of_positive_lower _ _ (by norm_num) paperC_floor_posDef
theorem paperR_posDef : paperR.PosDef :=
  posDef_of_positive_lower _ _ (by norm_num) paperR_lower_posDef
theorem paperS_posDef : paperS.PosDef :=
  posDef_of_positive_lower _ _ (by norm_num) paperS_lower_posDef

theorem matrix_power_lower {n : ℕ} (Q : Mat n) (c p : ℝ)
    (hc : 0 ≤ c) (hp : 0 ≤ p) (hQ : Q.PosSemidef) (hQc : c • (1 : Mat n) ≤ Q) :
    (c^p) • (1 : Mat n) ≤ spectralPower Q p := by
  rw [spectralPower, CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hQ.nonneg,
    ← Algebra.algebraMap_eq_smul_one]
  apply (algebraMap_le_cfc_iff (fun x : ℝ => x^p) (c^p) Q
    (Real.continuous_rpow_const hp).continuousOn hQ.isHermitian).mpr
  intro x hx
  have hcx := (algebraMap_le_iff_le_spectrum hQ.isHermitian).mp
    (show algebraMap ℝ (Mat n) c ≤ Q by simpa only [Algebra.algebraMap_eq_smul_one] using hQc) x hx
  exact Real.rpow_le_rpow hc hcx hp

theorem eighth_power_floor {n : ℕ} (Q : Mat n) (hQ : Q.PosDef)
    (hl : (9/20 : ℝ) • (1 : Mat n) ≤ Q) :
    (1/1024 : ℝ) • (1 : Mat n) ≤ Q^(8 : ℕ) := by
  have h := matrix_power_lower Q (9/20) ((8 : ℕ) : ℝ) (by norm_num)
    (by positivity) hQ.posSemidef hl
  rw [Real.rpow_natCast, spectralPower_nat Q hQ] at h
  exact (smul_le_smul_of_nonneg_right (by norm_num : (1/1024 : ℝ) ≤ (9/20)^8)
    (show (0 : Mat n) ≤ 1 from zero_le_one)).trans h

theorem paperR_eighth_floor : (1/1024 : ℝ) • (1 : Mat 3) ≤ paperR^8 :=
  eighth_power_floor _ paperR_posDef (Matrix.le_iff.mpr paperR_lower_posDef.posSemidef)
theorem paperS_eighth_floor : (1/1024 : ℝ) • (1 : Mat 3) ≤ paperS^8 :=
  eighth_power_floor _ paperS_posDef (Matrix.le_iff.mpr paperS_lower_posDef.posSemidef)

theorem eighth_root_pow {n : ℕ} (Q : Mat n) (hQ : Q.PosDef) :
    (spectralPower Q (1/8))^(8 : ℕ) = Q := by
  rw [← spectralPower_nat _ (spectralPower_posDef Q hQ (1/8)) 8]
  have h := CFC.rpow_rpow Q (1/8 : ℝ) (8 : ℝ) (by norm_num) hQ.isStrictlyPositive
  change spectralPower (spectralPower Q (1/8)) 8 = spectralPower Q ((1/8)*8) at h
  norm_num only [Nat.cast_ofNat]
  rw [h]
  norm_num only [one_div, inv_mul_cancel₀ (by norm_num : (8 : ℝ) ≠ 0)]
  exact spectralPower_one Q hQ

theorem eighth_root_norm_lt {n : ℕ} (Q : Mat n) (hQ : Q.PosDef)
    (K : ℝ) (hK : 0 < K) (htrace : Q.trace.re < K^8) :
    operatorNorm (spectralPower Q (1/8)) < K := by
  have hpow : operatorNorm (spectralPower Q (1/8))^8 < K^8 := by
    rw [← operatorNorm_eighth_power _ (spectralPower_posDef Q hQ (1/8)).isHermitian,
      eighth_root_pow Q hQ]
    exact (operatorNorm_posSemidef_le_trace Q hQ.posSemidef).trans_lt htrace
  exact (pow_lt_pow_iff_left₀ (operatorNorm_nonneg _) hK.le (by norm_num : (8 : ℕ) ≠ 0)).mp hpow

theorem paperX_norm_lt : operatorNorm (spectralPower paperC (1/8)) < 8 :=
  eighth_root_norm_lt _ paperC_posDef _ (by norm_num) paperC_trace_lt
theorem paperY_norm_lt : operatorNorm (spectralPower paperB (1/8)) < 4 :=
  eighth_root_norm_lt _ paperB_posDef _ (by norm_num) paperB_trace_lt

#print axioms paperR_eighth_floor
#print axioms paperS_eighth_floor
#print axioms paperX_norm_lt
#print axioms paperY_norm_lt
end NLA.MI22.Paper
