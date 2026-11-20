module

public import NLA.RA02.PaperInterpolationLift

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

def lowerOperator (n : ℕ) (t : ℝ) := Matrix.toEuclideanCLM (𝕜 := ℝ) (lower n t)

theorem continuous_lowerOperator (n : ℕ) : Continuous (lowerOperator n) :=
  continuous_real_euclidean_operator.comp (continuous_lower n)

theorem lowerOperator_zero (n : ℕ) : lowerOperator n 0 = 1 := by
  simp [lowerOperator, lower_zero]

theorem lowerOperator_near_identity (n : ℕ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ‖lowerOperator n t - 1‖ ≤ 1/2 := by
  have hc : Continuous (fun t : ℝ => ‖lowerOperator n t - 1‖) :=
    ((continuous_lowerOperator n).sub continuous_const).norm
  have he := hc.continuousAt.eventually (gt_mem_nhds
    (show ‖lowerOperator n 0 - 1‖ < (1/2 : ℝ) by rw [lowerOperator_zero]; norm_num))
  filter_upwards [he.filter_mono inf_le_left] with t ht
  exact ht.le

theorem norm_le_twice_image {n : ℕ} (F : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hF : ‖F - 1‖ ≤ 1/2) (v : EuclideanSpace ℝ (Fin n)) : ‖v‖ ≤ 2*‖F v‖ := by
  have hb : ‖v-F v‖ ≤ ‖F-1‖*‖v‖ := by
    calc
      _ = ‖(F-1) v‖ := by simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, norm_sub_rev]
      _ ≤ _ := (F-1).le_opNorm v
  have ht : ‖v‖ ≤ ‖F v‖+‖v-F v‖ := by
    simpa only [add_sub_cancel] using norm_add_le (F v) (v-F v)
  have hm := mul_le_mul_of_nonneg_right hF (norm_nonneg v)
  linarith

theorem lowerOperator_lift {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    lowerOperator n t (WithLp.toLp 2 (liftedInterpolationVector hs rows t)) =
      WithLp.toLp 2 (interpolationResidual hs rows t) := by
  change WithLp.toLp 2 (lower n t *ᵥ liftedInterpolationVector hs rows t) = _
  rw [interpolation_as_lower_mulVec]

theorem lifted_norm_ge_one {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    1 ≤ ‖(WithLp.toLp 2 (liftedInterpolationVector hs rows t) : EuclideanSpace ℝ (Fin n))‖ := by
  have he := PiLp.norm_apply_le (WithLp.toLp 2 (liftedInterpolationVector hs rows t)) (⟨s,hs⟩ : Fin n)
  change ‖liftedInterpolationVector hs rows t ⟨s,hs⟩‖ ≤ _ at he
  simpa only [lifted_next_entry, norm_one] using he

theorem interpolation_norm_lower_bound {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, (1/4 : ℝ) ≤ interpolationSquaredNorm hs rows t := by
  filter_upwards [lowerOperator_near_identity n] with t ht
  have hb := norm_le_twice_image (lowerOperator n t) ht
    (WithLp.toLp 2 (liftedInterpolationVector hs rows t))
  rw [lowerOperator_lift] at hb
  have hv := lifted_norm_ge_one hs rows t
  have hw := norm_nonneg (WithLp.toLp 2 (interpolationResidual hs rows t) : EuclideanSpace ℝ (Fin n))
  rw [← interpolation_actual_squared_norm]
  nlinarith

#print axioms interpolation_norm_lower_bound
end NLA.RA02.Paper
