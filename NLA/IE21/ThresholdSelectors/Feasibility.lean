module

public import NLA.IE21.ThresholdSelectors.Definitions
public import NLA.IE21.ThresholdSelectors.Quantile
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace NLA.IE21.ThresholdSelectors

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {Y : Ω → ℝ} {θ : ℝ}

theorem feasible_integrable {w : Ω → ℝ} (hw : Feasible μ θ w) : Integrable w μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ)) hw.1.aestronglyMeasurable
  exact Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hw.2.1 ω).1] using (hw.2.1 ω).2

theorem thresholdWeight_measurable (hY : Measurable Y) (q c : ℝ) :
    Measurable (thresholdWeight Y q c) := by
  unfold thresholdWeight
  exact Measurable.ite (measurableSet_lt hY measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun hY measurable_const) measurable_const measurable_const)

omit [MeasurableSpace Ω] in
theorem thresholdWeight_bounds (q : ℝ) {c : ℝ} (hc : 0 ≤ c ∧ c ≤ 1) (ω : Ω) :
    0 ≤ thresholdWeight Y q c ω ∧ thresholdWeight Y q c ω ≤ 1 := by
  unfold thresholdWeight
  split_ifs <;> simp_all

theorem thresholdWeight_integral (hY : Measurable Y) (q c : ℝ) :
    (∫ ω, thresholdWeight Y q c ω ∂μ) =
      μ.real {ω | Y ω < q} + c * μ.real {ω | Y ω = q} := by
  have hlt : MeasurableSet {ω | Y ω < q} := measurableSet_lt hY measurable_const
  have heq : MeasurableSet {ω | Y ω = q} := measurableSet_eq_fun hY measurable_const
  have hw : thresholdWeight Y q c = fun ω =>
      {ω | Y ω < q}.indicator (fun _ => (1 : ℝ)) ω +
        {ω | Y ω = q}.indicator (fun _ => c) ω := by
    funext ω
    by_cases hl : Y ω < q
    · have hn : Y ω ≠ q := ne_of_lt hl
      simp [thresholdWeight, hl, hn]
    · by_cases he : Y ω = q <;> simp [thresholdWeight, hl, he]
  rw [hw, integral_add ((integrable_const 1).indicator hlt) ((integrable_const c).indicator heq),
    integral_indicator hlt, integral_indicator heq]
  simp only [setIntegral_const, smul_eq_mul, mul_one]
  ring

theorem exists_feasible_threshold (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hθ : 0 < θ ∧ θ < 1) :
    ∃ q c : ℝ, 0 ≤ q ∧ (0 ≤ c ∧ c ≤ 1) ∧ Feasible μ θ (thresholdWeight Y q c) := by
  let : IsProbabilityMeasure (μ.map Y) := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  obtain ⟨q, hlo, hhi⟩ := exists_quantile_bracket (μ.map Y) θ hθ
  rw [map_measureReal_apply hY measurableSet_Iio] at hlo
  rw [map_measureReal_apply hY measurableSet_Iic] at hhi
  change μ.real {ω | Y ω < q} ≤ θ at hlo
  change θ ≤ μ.real {ω | Y ω ≤ q} at hhi
  have hq : 0 ≤ q := by
    by_contra hn
    have he : {ω | Y ω ≤ q} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun hy => (not_le_of_gt (lt_of_not_ge hn)) ((hY0 ω).trans hy)
    rw [he, measureReal_empty] at hhi
    linarith [hθ.1]
  let a := μ.real {ω | Y ω < q}
  let b := μ.real {ω | Y ω = q}
  have hab : θ ≤ a + b := by
    have hu : {ω | Y ω ≤ q} = {ω | Y ω < q} ∪ {ω | Y ω = q} := by
      ext ω
      simp only [mem_ofPred_eq, mem_union]
      exact le_iff_lt_or_eq
    rw [hu, measureReal_union] at hhi
    · exact hhi
    · exact Set.disjoint_left.mpr fun ω hl he => (ne_of_lt hl) he
    · exact measurableSet_eq_fun hY measurable_const
  have hb : 0 ≤ b := measureReal_nonneg
  let c := if b = 0 then 0 else (θ - a) / b
  have hc : 0 ≤ c ∧ c ≤ 1 := by
    by_cases hb0 : b = 0
    · simp [c, hb0]
    · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      simp only [c, hb0, ↓reduceIte]
      constructor
      · exact div_nonneg (sub_nonneg.mpr hlo) hb
      · exact (div_le_one hbpos).mpr (by linarith)
  have hmass : a + c * b = θ := by
    by_cases hb0 : b = 0
    · simp only [c, hb0, ↓reduceIte, mul_zero, add_zero]
      linarith
    · simp only [c, hb0, ↓reduceIte]
      rw [div_mul_cancel₀ _ hb0]
      ring
  refine ⟨q, c, hq, hc, thresholdWeight_measurable hY q c,
    thresholdWeight_bounds q hc, ?_⟩
  rw [thresholdWeight_integral hY]
  exact hmass

#print axioms exists_feasible_threshold

end NLA.IE21.ThresholdSelectors
