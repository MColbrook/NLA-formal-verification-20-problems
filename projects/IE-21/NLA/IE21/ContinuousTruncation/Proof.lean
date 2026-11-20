module

public import NLA.IE21.QuantileIntegral.Representation

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace NLA.IE21.ContinuousTruncation
open QuantileIntegral ThresholdSelectors

theorem lowerQuantile_open_mass_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    μ.real (Iio (lowerQuantile μ θ)) ≤ θ := by
  have hl (x : ℝ) (hx : x < lowerQuantile μ θ) : cdf μ x < θ := by
    by_contra hn
    exact (not_le_of_gt hx) ((lowerQuantile_le_iff μ hθ).mpr (le_of_not_gt hn))
  have hlim : Function.leftLim (cdf μ) (lowerQuantile μ θ) ≤ θ := by
    exact le_of_tendsto ((monotone_cdf μ).tendsto_leftLim _)
      (eventually_mem_nhdsWithin.mono fun x hx => (hl x hx).le)
  have hlim0 : 0 ≤ Function.leftLim (cdf μ) (lowerQuantile μ θ) := by
    exact ge_of_tendsto ((monotone_cdf μ).tendsto_leftLim _)
      (Eventually.of_forall (cdf_nonneg μ))
  have heq : μ.real (Iio (lowerQuantile μ θ)) = Function.leftLim (cdf μ) (lowerQuantile μ θ) := by
    unfold Measure.real
    have hm := (cdf μ).measure_Iio (tendsto_cdf_atBot μ) (lowerQuantile μ θ)
    rw [measure_cdf, sub_zero] at hm
    rw [hm, ENNReal.toReal_ofReal hlim0]
  exact heq ▸ hlim

/-- A law without atoms assigns exactly the requested mass to its actual
generalized-inverse quantile. No quantile mass is assumed. -/
theorem atomless_lowerQuantile_mass (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    μ.real (Iic (lowerQuantile μ θ)) = θ := by
  have hlo := lowerQuantile_open_mass_le μ θ hθ
  have hhi := le_cdf_lowerQuantile μ hθ
  rw [cdf_eq_real] at hhi
  have he : μ.real (Iio (lowerQuantile μ θ)) = μ.real (Iic (lowerQuantile μ θ)) :=
    measureReal_congr Iio_ae_eq_Iic
  rw [he] at hlo
  exact le_antisymm hlo hhi

theorem continuous_law_truncated_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) [NullSingletonClass (μ.map Y)]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    let b := lowerQuantile (μ.map Y) θ
    0 ≤ b ∧ μ.real {ω | Y ω ≤ b} = θ ∧
      Integrable ({ω | Y ω ≤ b}.indicator Y) μ ∧
      populationTrim θ μ Y = ∫ ω, {ω | Y ω ≤ b}.indicator Y ω ∂μ ∧
      primalTrim θ μ Y = ENNReal.ofReal (∫ ω, {ω | Y ω ≤ b}.indicator Y ω ∂μ) := by
  let b := lowerQuantile (μ.map Y) θ
  have hp : IsProbabilityMeasure (μ.map Y) := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  have hn : ∀ᵐ y ∂μ.map Y, 0 ≤ y :=
    (ae_map_iff hY.aemeasurable measurableSet_Ici).mpr (Eventually.of_forall hY0)
  have hb : 0 ≤ b := lowerQuantile_nonneg (μ.map Y) hn hθ
  have hmass : μ.real {ω | Y ω ≤ b} = θ := by
    have h := atomless_lowerQuantile_mass (μ.map Y) θ hθ
    rw [map_measureReal_apply hY measurableSet_Iic] at h
    exact h
  have hset : MeasurableSet {ω | Y ω ≤ b} := measurableSet_le hY measurable_const
  have hw : thresholdWeight Y b 1 = {ω | Y ω ≤ b}.indicator (fun _ => 1) := by
    funext ω
    by_cases hlt : Y ω < b
    · simp [thresholdWeight, hlt, hlt.le]
    · by_cases he : Y ω = b
      · simp [thresholdWeight, hlt, he]
      · have hgt : ¬ Y ω ≤ b := fun h => he (le_antisymm h (le_of_not_gt hlt))
        simp [thresholdWeight, hlt, he, hgt]
  have hf : Feasible μ θ (thresholdWeight Y b 1) := by
    refine ⟨thresholdWeight_measurable hY b 1, thresholdWeight_bounds b ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [hw, integral_indicator hset, setIntegral_const, hmass]
    simp
  have he : (fun ω => Y ω * thresholdWeight Y b 1 ω) = {ω | Y ω ≤ b}.indicator Y := by
    rw [hw]
    funext ω
    by_cases h : Y ω ≤ b <;> simp [h]
  have hi := threshold_selected_integrable hY hY0 hb (show 0 ≤ (1 : ℝ) ∧ 1 ≤ 1 by norm_num) (μ := μ)
  have hv := populationTrim_eq_threshold_cost hY hY0 hb (show 0 ≤ (1 : ℝ) ∧ 1 ≤ 1 by norm_num) hf
  rw [he] at hi hv
  refine ⟨hb, hmass, hi, hv, ?_⟩
  rw [primalTrim_eq_populationTrim hY hY0 hθ, hv]

#print axioms lowerQuantile_open_mass_le
#print axioms atomless_lowerQuantile_mass
#print axioms continuous_law_truncated_expectation
end NLA.IE21.ContinuousTruncation
