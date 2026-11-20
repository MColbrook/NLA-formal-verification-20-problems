module

public import NLA.RA02.PaperInterpolationNorm

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem selected_residual_next_zero {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (hm : (⟨s,hs⟩ : Fin n) ∈ Set.range rows) (t : ℝ)
    (hu : IsUnit (prefixMatrix hs.le rows t)) : interpolationResidual hs rows t ⟨s,hs⟩ = 0 := by
  obtain ⟨i,hi⟩ := hm
  simpa only [hi] using interpolation_vanishes_on_rows hs rows t hu i

theorem selected_reciprocal_bound {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (hm : (⟨s,hs⟩ : Fin n) ∈ Set.range rows) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (interpolationSquaredNorm hs rows t)⁻¹ ≤ 4*‖lowerOperator n t-1‖^2 := by
  filter_upwards [lowerOperator_near_identity n, interpolation_norm_lower_bound hs rows,
    prefix_eventually_nonsingular hs.le rows] with t hnear hlow hdet
  have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (liftedInterpolationVector hs rows t)
  let w : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (interpolationResidual hs rows t)
  let F := lowerOperator n t
  have he : ((F-1) v) ⟨s,hs⟩ = -1 := by
    change (lower n t *ᵥ liftedInterpolationVector hs rows t) ⟨s,hs⟩ -
      liftedInterpolationVector hs rows t ⟨s,hs⟩ = -1
    rw [interpolation_as_lower_mulVec, selected_residual_next_zero hs rows hm t hu, lifted_next_entry]
    norm_num
  have hc : 1 ≤ ‖(F-1) v‖ := by
    have hh := PiLp.norm_apply_le ((F-1) v) (⟨s,hs⟩ : Fin n)
    simpa only [he, norm_neg, norm_one] using hh
  have hvw : ‖v‖ ≤ 2*‖w‖ := by
    simpa only [v, F, lowerOperator_lift] using norm_le_twice_image F hnear v
  have hopen := (F-1).le_opNorm v
  have hh : 1 ≤ 2*‖F-1‖*‖w‖ := by
    have hmul := mul_le_mul_of_nonneg_left hvw (norm_nonneg (F-1))
    nlinarith
  have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hh
  have hw : ‖w‖^2 = interpolationSquaredNorm hs rows t := interpolation_actual_squared_norm hs rows t
  have hprod : 1 ≤ (4*‖F-1‖^2) * interpolationSquaredNorm hs rows t := by
    rw [← hw]
    nlinarith
  have hp : 0 < interpolationSquaredNorm hs rows t := by linarith
  rw [← one_div, div_le_iff₀ hp]
  exact hprod

theorem interpolation_selected_reciprocal_limit {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n)
    (hm : (⟨s,hs⟩ : Fin n) ∈ Set.range rows) :
    Tendsto (fun t => (interpolationSquaredNorm hs rows t)⁻¹) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (fun t : ℝ => (4 : ℝ)*‖lowerOperator n t-1‖^2) :=
    (((continuous_lowerOperator n).sub continuous_const).norm.pow 2).const_mul 4
  have ht : Tendsto (fun t : ℝ => (4 : ℝ)*‖lowerOperator n t-1‖^2) (𝓝[>] 0) (𝓝 0) := by
    simpa only [lowerOperator_zero, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      hc.continuousAt.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply squeeze_zero' _ (selected_reciprocal_bound hs rows hm) ht
  filter_upwards [interpolation_norm_lower_bound hs rows] with t ht
  exact inv_nonneg.mpr (by linarith)

#print axioms interpolation_selected_reciprocal_limit
end NLA.RA02.Paper
