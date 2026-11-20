module

public import NLA.IE21.ThresholdSelectors.Feasibility

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace NLA.IE21.ThresholdSelectors

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : Ω → ℝ} {θ q c : ℝ}

theorem threshold_selected_bound (hY0 : ∀ ω, 0 ≤ Y ω) (hq : 0 ≤ q)
    (hc : 0 ≤ c ∧ c ≤ 1) (ω : Ω) :
    0 ≤ Y ω * thresholdWeight Y q c ω ∧ Y ω * thresholdWeight Y q c ω ≤ q := by
  constructor
  · exact mul_nonneg (hY0 ω) (thresholdWeight_bounds q hc ω).1
  · by_cases hl : Y ω < q
    · simpa [thresholdWeight, hl] using hl.le
    · by_cases he : Y ω = q
      · simp only [thresholdWeight, he, lt_self_iff_false, ↓reduceIte]
        nlinarith [mul_nonneg hq (sub_nonneg.mpr hc.2)]
      · simp [thresholdWeight, hl, he, hq]

theorem threshold_selected_integrable (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hq : 0 ≤ q) (hc : 0 ≤ c ∧ c ≤ 1) :
    Integrable (fun ω => Y ω * thresholdWeight Y q c ω) μ := by
  apply Integrable.mono' (integrable_const q)
    ((hY.mul (thresholdWeight_measurable hY q c)).aestronglyMeasurable)
  filter_upwards with ω
  change |Y ω * thresholdWeight Y q c ω| ≤ q
  simpa only [abs_of_nonneg (threshold_selected_bound hY0 hq hc ω).1]
    using (threshold_selected_bound hY0 hq hc ω).2

theorem threshold_exchange_inequality (hY0 : ∀ ω, 0 ≤ Y ω) (hq : 0 ≤ q)
    (hc : 0 ≤ c ∧ c ≤ 1) {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω ∧ w ω ≤ 1) (ω : Ω) :
    Y ω * thresholdWeight Y q c ω + q * w ω ≤
      Y ω * w ω + q * thresholdWeight Y q c ω := by
  by_cases hl : Y ω < q
  · simp only [thresholdWeight, hl, ↓reduceIte, mul_one]
    nlinarith [mul_nonneg (sub_nonneg.mpr hl.le) (sub_nonneg.mpr (hw ω).2)]
  · by_cases he : Y ω = q
    · simp [thresholdWeight, hl, he, add_comm]
    · simp only [thresholdWeight, hl, he, ↓reduceIte, mul_zero, zero_add, add_zero]
      exact mul_le_mul_of_nonneg_right (le_of_not_gt hl) (hw ω).1

/-- Fractional selection at a quantile minimizes the extended nonnegative
expectation, without requiring the full random variable to have a finite mean. -/
theorem threshold_optimal (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hq : 0 ≤ q) (hc : 0 ≤ c ∧ c ≤ 1)
    (hs : Feasible μ θ (thresholdWeight Y q c)) {w : Ω → ℝ} (hw : Feasible μ θ w) :
    selectorCost μ Y (thresholdWeight Y q c) ≤ selectorCost μ Y w := by
  have hmass {v : Ω → ℝ} (hv : Feasible μ θ v) :
      (∫⁻ ω, ENNReal.ofReal (q * v ω) ∂μ) = ENNReal.ofReal (q * θ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((feasible_integrable hv).const_mul q)
      (Eventually.of_forall fun ω => mul_nonneg hq (hv.2.1 ω).1)]
    rw [integral_const_mul, hv.2.2]
  apply ENNReal.le_of_add_le_add_right (a := ENNReal.ofReal (q * θ)) ENNReal.ofReal_ne_top
  conv_lhs => rhs; rw [← hmass hw]
  conv_rhs => rhs; rw [← hmass hs]
  unfold selectorCost
  have hsm : Measurable (fun ω => ENNReal.ofReal (Y ω * thresholdWeight Y q c ω)) := (hY.mul hs.1).ennreal_ofReal
  have hwm : Measurable (fun ω => ENNReal.ofReal (Y ω * w ω)) := (hY.mul hw.1).ennreal_ofReal
  rw [← lintegral_add_left hsm, ← lintegral_add_left hwm]
  apply lintegral_mono
  intro ω
  dsimp only
  rw [← ENNReal.ofReal_add (mul_nonneg (hY0 ω) (hs.2.1 ω).1)
      (mul_nonneg hq (hw.2.1 ω).1),
    ← ENNReal.ofReal_add (mul_nonneg (hY0 ω) (hw.2.1 ω).1)
      (mul_nonneg hq (hs.2.1 ω).1)]
  exact ENNReal.ofReal_le_ofReal (threshold_exchange_inequality hY0 hq hc hw.2.1 ω)

theorem exists_primal_minimizer (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hθ : 0 < θ ∧ θ < 1) :
    ∃ q c : ℝ, 0 ≤ q ∧ (0 ≤ c ∧ c ≤ 1) ∧ Feasible μ θ (thresholdWeight Y q c) ∧
      primalTrim θ μ Y = selectorCost μ Y (thresholdWeight Y q c) ∧
      selectorCost μ Y (thresholdWeight Y q c) < ∞ := by
  obtain ⟨q, c, hq, hc, hs⟩ := exists_feasible_threshold hY hY0 hθ (μ := μ)
  refine ⟨q, c, hq, hc, hs, ?_, ?_⟩
  · apply le_antisymm
    · exact sInf_le ⟨thresholdWeight Y q c, hs, rfl⟩
    · apply le_sInf
      rintro z ⟨w, hw, rfl⟩
      exact threshold_optimal hY hY0 hq hc hs hw
  · unfold selectorCost
    rw [← ofReal_integral_eq_lintegral_ofReal (threshold_selected_integrable hY hY0 hq hc)
      (Eventually.of_forall fun ω => (threshold_selected_bound hY0 hq hc ω).1)]
    exact ENNReal.ofReal_lt_top

#print axioms threshold_optimal
#print axioms exists_primal_minimizer

end NLA.IE21.ThresholdSelectors
