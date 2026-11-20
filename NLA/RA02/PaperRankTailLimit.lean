module

public import NLA.RA02.PaperTailDefinitions
public import NLA.RA02.PaperComplexInverse
public import NLA.RA02.PaperInverseSpectrum
public import NLA.RA02.PaperHistoryLimits

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology ComplexOrder
open Filter
namespace NLA.RA02.Paper

theorem familyRankTail_eq_last (r : ℕ) {t : ℝ} (ht : 0 < t) :
    familyRankTail r t = NLA.RA02.orderedEigenvalues (complexify (sharpFamily (r+1) t))
      (complexify_posDef _ (sharpFamily_posDef _ _ ht)).isHermitian (Fin.last r) := by
  rw [familyRankTail, dif_pos (complexify_posDef _ (sharpFamily_posDef _ _ ht)).isHermitian,
    NLA.RA02.rankTail_last]

theorem familyRankTail_positive (r : ℕ) {t : ℝ} (ht : 0 < t) : 0 < familyRankTail r t := by
  rw [familyRankTail_eq_last r ht]
  exact NLA.RA02.orderedEigenvalues_pos _ (complexify_posDef _ (sharpFamily_posDef _ _ ht)) _ _

theorem family_inverse_norm_ratio (r : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖Matrix.toEuclideanCLM (𝕜:=ℂ) (complexify (scaledFamilyInverse r t))‖ =
      epsilon (r+1) t^r / familyRankTail r t := by
  have he : 0 < epsilon (r+1) t := pow_pos ht _
  have hu : IsUnit (sharpFamily (r+1) t) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    rw [isUnit_iff_ne_zero, sharpFamily_det]
    exact pow_ne_zero _ (ne_of_gt he)
  rw [scaledFamilyInverse_eq r (ne_of_gt ht), complexify_smul, complexify_inverse _ hu,
    map_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos he r),
    inverse_norm_last_eigenvalue r _ (complexify_posDef _ (sharpFamily_posDef _ _ ht)),
    familyRankTail_eq_last r ht, div_eq_mul_inv]

theorem familyRankTail_epsilon_limit (r : ℕ) :
    Tendsto (fun t : ℝ => familyRankTail r t / epsilon (r+1) t^r) (𝓝[>] 0) (𝓝 1) := by
  have hh : Tendsto (fun t : ℝ => epsilon (r+1) t^r / familyRankTail r t) (𝓝[>] 0) (𝓝 1) := by
    apply (complex_scaled_inverse_norm_limit r).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact family_inverse_norm_ratio r ht
  simpa only [inv_div, inv_one] using hh.inv₀ one_ne_zero

theorem sharp_cholesky_rankTail_limit (r : ℕ) :
    Tendsto (fun t : ℝ => NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r /
      familyRankTail r t) (𝓝[>] 0) (𝓝 ((2 : ℝ)^r)) := by
  have hh := (sharp_cholesky_epsilon_limit r).div (familyRankTail_epsilon_limit r) one_ne_zero
  simp only [div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have he : epsilon (r+1) t ≠ 0 := pow_ne_zero _ (ne_of_gt (show 0 < t from ht))
  change (NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r / epsilon (r+1) t^r) /
    (familyRankTail r t / epsilon (r+1) t^r) = _
  rw [div_div_div_cancel_right₀ (pow_ne_zero r he)]

#print axioms sharp_cholesky_rankTail_limit
end NLA.RA02.Paper
