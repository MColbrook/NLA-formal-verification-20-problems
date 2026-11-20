module

public import NLA.IE21.ThresholdSelectors.Optimality
public import NLA.IE21.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace NLA.IE21.ThresholdSelectors

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : Ω → ℝ} {θ q c : ℝ}

theorem nonnegative_hinge_integrable (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    {t : ℝ} (ht : 0 ≤ t) : Integrable (fun ω => max (t - Y ω) 0) μ := by
  apply Integrable.mono' (integrable_const t) (by fun_prop)
  filter_upwards with ω
  simp only [Real.norm_eq_abs, abs_of_nonneg (le_max_right (t - Y ω) 0)]
  exact max_le (by linarith [hY0 ω]) ht

theorem threshold_hinge_identity (ω : Ω) :
    Y ω * thresholdWeight Y q c ω =
      q * thresholdWeight Y q c ω - max (q - Y ω) 0 := by
  by_cases hl : Y ω < q
  · simp only [thresholdWeight, hl, ↓reduceIte, mul_one, max_eq_left (sub_nonneg.mpr hl.le)]
    ring
  · by_cases he : Y ω = q
    · simp [thresholdWeight, hl, he]
    · simp only [thresholdWeight, hl, he, ↓reduceIte, mul_zero,
        max_eq_right (sub_nonpos.mpr (le_of_not_gt hl)), sub_zero]

theorem populationTrim_eq_threshold_cost (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hq : 0 ≤ q) (hc : 0 ≤ c ∧ c ≤ 1)
    (hs : Feasible μ θ (thresholdWeight Y q c)) :
    populationTrim θ μ Y = ∫ ω, Y ω * thresholdWeight Y q c ω ∂μ := by
  have hsi := feasible_integrable hs
  have hYi := threshold_selected_integrable hY hY0 hq hc (μ := μ)
  have hbound (t : ℝ) (ht : 0 ≤ t) :
      θ * t - (∫ ω, max (t - Y ω) 0 ∂μ) ≤
        ∫ ω, Y ω * thresholdWeight Y q c ω ∂μ := by
    have hi := integral_mono ((hsi.const_mul t).sub hYi)
      (nonnegative_hinge_integrable hY hY0 ht) (fun ω => ?_)
    · simp only [Pi.sub_apply] at hi
      rw [integral_sub (hsi.const_mul t) hYi, integral_const_mul, hs.2.2] at hi
      nlinarith
    · change t * thresholdWeight Y q c ω - Y ω * thresholdWeight Y q c ω ≤ max (t - Y ω) 0
      have hb := hs.2.1 ω
      by_cases hty : Y ω ≤ t
      · rw [max_eq_left (sub_nonneg.mpr hty)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hty) (sub_nonneg.mpr hb.2)]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hty))]
        nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hty)) hb.1]
  have hnonempty : {z | ∃ t : ℝ, 0 ≤ t ∧ z = θ * t - ∫ ω, max (t - Y ω) 0 ∂μ}.Nonempty :=
    ⟨_, 0, le_rfl, rfl⟩
  have hbounded : BddAbove {z | ∃ t : ℝ, 0 ≤ t ∧ z = θ * t - ∫ ω, max (t - Y ω) 0 ∂μ} := by
    refine ⟨∫ ω, Y ω * thresholdWeight Y q c ω ∂μ, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    exact hbound t ht
  have hattain : (∫ ω, Y ω * thresholdWeight Y q c ω ∂μ) =
      θ * q - ∫ ω, max (q - Y ω) 0 ∂μ := by
    simp_rw [threshold_hinge_identity]
    rw [integral_sub (hsi.const_mul q) (nonnegative_hinge_integrable hY hY0 hq),
      integral_const_mul, hs.2.2, mul_comm q θ]
  apply le_antisymm
  · apply csSup_le hnonempty
    rintro z ⟨t, ht, rfl⟩
    exact hbound t ht
  · rw [hattain]
    exact le_csSup hbounded ⟨q, hq, rfl⟩

/-- The manuscript's selector infimum and threshold supremum agree, for every
nonnegative measurable random variable, even with infinite untrimmed mean. -/
theorem primalTrim_eq_populationTrim (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hθ : 0 < θ ∧ θ < 1) :
    primalTrim θ μ Y = ENNReal.ofReal (populationTrim θ μ Y) := by
  obtain ⟨q, c, hq, hc, hs, hmin, _⟩ := exists_primal_minimizer hY hY0 hθ (μ := μ)
  rw [hmin, populationTrim_eq_threshold_cost hY hY0 hq hc hs]
  exact (ofReal_integral_eq_lintegral_ofReal (threshold_selected_integrable hY hY0 hq hc)
    (Eventually.of_forall fun ω => (threshold_selected_bound hY0 hq hc ω).1)).symm

theorem populationTrim_nonneg (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hθ : 0 < θ ∧ θ < 1) : 0 ≤ populationTrim θ μ Y := by
  obtain ⟨q, c, hq, hc, hs⟩ := exists_feasible_threshold hY hY0 hθ (μ := μ)
  rw [populationTrim_eq_threshold_cost hY hY0 hq hc hs]
  exact integral_nonneg (fun ω => (threshold_selected_bound hY0 hq hc ω).1)

#print axioms populationTrim_eq_threshold_cost
#print axioms primalTrim_eq_populationTrim

#print axioms populationTrim_nonneg

end NLA.IE21.ThresholdSelectors
