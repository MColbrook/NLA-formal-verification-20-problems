module

public import NLA.IE21.ContinuousTruncation.Proof
public import NLA.IE21.TrimmingConcentration
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators ENNReal
namespace NLA.IE21.LiteralWrappers
open QuantileIntegral ContinuousTruncation

theorem actual_quantile_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hmean : ∫ ω, Y ω ∂μ = 1) [NullSingletonClass (μ.map Y)]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    let b := lowerQuantile (μ.map Y) θ
    0 < b ∧ b ≤ 1 / (1-θ) ∧ b ≤ truncationScale θ ∧
      μ.real {ω | Y ω ≤ b} = θ ∧
      populationTrim θ μ Y = ∫ ω, {ω | Y ω ≤ b}.indicator Y ω ∂μ := by
  let b := lowerQuantile (μ.map Y) θ
  have hb := continuous_law_truncated_expectation μ Y hYm hY0 θ hθ
  have hp : IsProbabilityMeasure (μ.map Y) := (Measure.isProbabilityMeasure_map_iff hYm.aemeasurable).mpr inferInstance
  have hbpos : 0 < b := by
    by_contra hnot
    have hb0 : b = 0 := le_antisymm (le_of_not_gt hnot) hb.1
    have he : {ω | Y ω ≤ b} = Y ⁻¹' {0} := by
      ext ω
      simp only [mem_setOf_eq, mem_preimage, mem_singleton_iff, hb0]
      exact ⟨fun h => le_antisymm h (hY0 ω), fun h => h.le⟩
    have hm : μ (Y ⁻¹' {0}) = 0 := by
      rw [← Measure.map_apply hYm (measurableSet_singleton 0)]
      exact measure_singleton 0
    have hz : μ.real {ω | Y ω ≤ b} = 0 := by rw [he]; simp [Measure.real, hm]
    have : θ = 0 := hb.2.1.symm.trans hz
    linarith [hθ.1]
  obtain ⟨c, hc, hcu, hcl, hcr⟩ := exists_bounded_quantile μ Y hYm hY hY0 hmean θ hθ
  have hbc : b ≤ c := by
    apply (lowerQuantile_le_iff (μ.map Y) hθ).mpr
    rw [cdf_eq_real, map_measureReal_apply hYm measurableSet_Iic]
    exact hcr
  have hbu := hbc.trans hcu
  refine ⟨hbpos, hbu, hbu.trans ?_, hb.2.1, hb.2.2.2.1⟩
  unfold truncationScale
  exact div_le_div_of_nonneg_right (by norm_num) (sub_pos.mpr hθ.2).le

theorem mean_one_large_threshold_mass {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hYm : Measurable Y) (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hmean : ∫ ω, Y ω ∂μ = 1) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    (1 + θ) / 2 ≤ μ.real {ω | Y ω ≤ truncationScale θ} := by
  let L := truncationScale θ
  let C : Ω → ℝ := {ω | Y ω ≤ L}.indicator (fun _ => 1)
  have hθ1 : 0 < 1-θ := sub_pos.mpr hθ.2
  have hL : 0 < L := by dsimp [L, truncationScale]; positivity
  have hLeq : L * (1-θ) = 2 := by dsimp [L, truncationScale]; field_simp
  have hCm : Measurable C := measurable_const.indicator (measurableSet_le hYm measurable_const)
  have hCb (ω : Ω) : C ω ∈ Icc 0 1 := by dsimp [C, Set.indicator]; split_ifs <;> norm_num
  have hCi : Integrable C μ := Integrable.of_mem_Icc 0 1 hCm.aemeasurable (Eventually.of_forall hCb)
  have hi : ∫ ω, C ω ∂μ = μ.real {ω | Y ω ≤ L} := by simp [C, integral_indicator, measurableSet_le hYm measurable_const]
  have hh := integral_mono (((integrable_const (1 : ℝ)).sub hCi).const_mul L) hY (fun ω => ?_)
  · simp only [Pi.sub_apply] at hh
    rw [integral_const_mul, integral_sub (integrable_const (1 : ℝ)) hCi,
      integral_const, probReal_univ, smul_eq_mul, one_mul, hmean, hi] at hh
    nlinarith
  · dsimp [C, Set.indicator]
    split_ifs with hy
    · simpa using hY0 ω
    · simpa using (le_of_lt (lt_of_not_ge hy))

theorem mean_one_trim_le_theta {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Integrable Y μ) (hY0 : ∀ ω, 0 ≤ Y ω)
    (hmean : ∫ ω, Y ω ∂μ = 1) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    populationTrim θ μ Y ≤ θ := by
  apply csSup_le (populationTrim_objectives_nonempty θ Y)
  rintro z ⟨t, ht, rfl⟩
  have hh : (fun ω => θ * (t-Y ω)) ≤ (fun ω => max (t-Y ω) 0) := by
    intro ω
    change θ * (t-Y ω) ≤ max (t-Y ω) 0
    rcases le_total (t-Y ω) 0 with h | h
    · rw [max_eq_right h]
      exact mul_nonpos_of_nonneg_of_nonpos hθ.1.le h
    · rw [max_eq_left h]
      exact mul_le_of_le_one_left h hθ.2.le
  have hI := integral_mono (((integrable_const t).sub hY).const_mul θ)
    (trimming_hinge_integrable hY t) hh
  simp only [Pi.sub_apply] at hI
  rw [integral_const_mul, integral_sub (integrable_const t) hY, integral_const,
    probReal_univ, smul_eq_mul, one_mul, hmean] at hI
  linarith

#print axioms actual_quantile_bounds
#print axioms mean_one_trim_le_theta
end NLA.IE21.LiteralWrappers
