module

public import NLA.IE21.QuantileIntegral.InverseCDF
public import NLA.IE21.ThresholdSelectors.Duality

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace NLA.IE21.QuantileIntegral

theorem lowerQuantile_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) {u : ℝ} (hu : 0 < u ∧ u < 1) :
    0 ≤ lowerQuantile μ u := by
  by_contra hn
  have hq : lowerQuantile μ u < 0 := lt_of_not_ge hn
  have hz : μ (Iic (lowerQuantile μ u)) = 0 :=
    measure_mono_null (fun x hx => not_le_of_gt (lt_of_le_of_lt hx hq)) (ae_iff.mp hμ)
  have hc := le_cdf_lowerQuantile μ hu
  rw [cdf_eq_real, Measure.real, hz, ENNReal.toReal_zero] at hc
  exact (not_le_of_gt hu.1) hc

/-- The threshold supremum is the integral of the lower quantiles, including
laws with atoms and laws with infinite untrimmed first moment. -/
theorem populationTrim_eq_lowerQuantile_integral (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    populationTrim θ μ id = ∫ u in Ioc 0 θ, lowerQuantile μ u := by
  let ν : Measure ℝ := volume.restrict (Ioo 0 1)
  have hp : IsProbabilityMeasure ν := ⟨by simp [ν]⟩
  let Q := lowerQuantile μ
  let q := Q θ
  let w : ℝ → ℝ := (Iic θ).indicator (fun _ => 1)
  let F : ℝ → ℝ := (Iic θ).indicator Q
  have hQ : AEMeasurable Q ν := lowerQuantile_aemeasurable μ
  have hq : 0 ≤ q := lowerQuantile_nonneg μ hμ hθ
  have hQ0 : ∀ᵐ u ∂ν, 0 ≤ Q u :=
    (ae_restrict_mem measurableSet_Ioo).mono fun u hu => lowerQuantile_nonneg μ hμ hu
  have hw : Integrable w ν := (integrable_const (1 : ℝ)).indicator measurableSet_Iic
  have hwb (u : ℝ) : 0 ≤ w u ∧ w u ≤ 1 := by
    by_cases hu : u ≤ θ <;> simp [w, hu]
  have hwi : (∫ u, w u ∂ν) = θ := by
    rw [integral_indicator measurableSet_Iic, setIntegral_const]
    have he : Iic θ ∩ Ioo (0 : ℝ) 1 = Ioc 0 θ := by
      ext u
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans_lt hθ.2⟩⟩
    simp only [ν, measureReal_restrict_apply measurableSet_Iic, he,
      Real.volume_real_Ioc, sub_zero, max_eq_left hθ.1.le, smul_eq_mul, mul_one]
  have hFi : Integrable F ν := by
    apply Integrable.mono' (integrable_const q) (hQ.indicator measurableSet_Iic).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    by_cases ht : u ≤ θ
    · have h0 := lowerQuantile_nonneg μ hμ hu
      have hle := lowerQuantile_monotoneOn μ hu hθ ht
      simpa [F, ht, Q, q, abs_of_nonneg h0] using hle
    · simpa [F, ht] using hq
  have hFval : (∫ u, F u ∂ν) = ∫ u in Ioc 0 θ, Q u := by
    rw [integral_indicator measurableSet_Iic]
    have he : Iic θ ∩ Ioo (0 : ℝ) 1 = Ioc 0 θ := by
      ext u
      simp only [mem_inter_iff, mem_Iic, mem_Ioo, mem_Ioc]
      exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans_lt hθ.2⟩⟩
    simp only [ν, Measure.restrict_restrict measurableSet_Iic, he]
  have hhinge (t : ℝ) (ht : 0 ≤ t) : Integrable (fun u => max (t - Q u) 0) ν := by
    apply Integrable.mono' (integrable_const t)
      ((aemeasurable_const.sub hQ).max aemeasurable_const).aestronglyMeasurable
    filter_upwards [hQ0] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    change max (t - Q u) 0 ≤ t
    exact max_le (by linarith) ht
  have hmap (t : ℝ) : (∫ x, max (t - x) 0 ∂μ) = ∫ u, max (t - Q u) 0 ∂ν := by
    conv_lhs => rw [← lowerQuantile_map μ]
    exact integral_map hQ (by fun_prop)
  have hprod (u : ℝ) : F u = Q u * w u := by
    by_cases hu : u ≤ θ <;> simp [F, w, hu]
  have hupper (t : ℝ) (ht : 0 ≤ t) :
      θ * t - (∫ x, max (t - x) 0 ∂μ) ≤ ∫ u, F u ∂ν := by
    have he : ∀ u, t * w u - F u ≤ max (t - Q u) 0 := by
      intro u
      rw [hprod]
      have hb := hwb u
      by_cases hu : Q u ≤ t
      · rw [max_eq_left (sub_nonneg.mpr hu)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr hb.2)]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hu))]
        nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge hu)) hb.1]
    have hi := integral_mono ((hw.const_mul t).sub hFi) (hhinge t ht) he
    simp only [Pi.sub_apply] at hi
    rw [integral_sub (hw.const_mul t) hFi, integral_const_mul, hwi, ← hmap] at hi
    linarith
  have hattain : (∫ u, F u ∂ν) = θ * q - ∫ x, max (q - x) 0 ∂μ := by
    have he : F =ᵐ[ν] fun u => q * w u - max (q - Q u) 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      by_cases ht : u ≤ θ
      · have hle := lowerQuantile_monotoneOn μ hu hθ ht
        simp [F, w, ht, Q, q, max_eq_left (sub_nonneg.mpr hle)]
      · have hge := lowerQuantile_monotoneOn μ hθ hu (le_of_not_ge ht)
        simp [F, w, ht, Q, q, max_eq_right (sub_nonpos.mpr hge)]
    rw [integral_congr_ae he, integral_sub (hw.const_mul q) (hhinge q hq),
      integral_const_mul, hwi, ← hmap, mul_comm q θ]
  rw [← hFval]
  have hn : {z | ∃ t : ℝ, 0 ≤ t ∧ z = θ * t - ∫ x, max (t - x) 0 ∂μ}.Nonempty :=
    ⟨_, 0, le_rfl, rfl⟩
  have hb : BddAbove {z | ∃ t : ℝ, 0 ≤ t ∧ z = θ * t - ∫ x, max (t - x) 0 ∂μ} := by
    refine ⟨∫ u, F u ∂ν, ?_⟩
    rintro z ⟨t, ht, rfl⟩
    exact hupper t ht
  apply le_antisymm
  · apply csSup_le hn
    rintro z ⟨t, ht, rfl⟩
    exact hupper t ht
  · rw [hattain]
    exact le_csSup hb ⟨q, hq, rfl⟩

theorem primalTrim_eq_lowerQuantile_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ThresholdSelectors.primalTrim θ μ Y =
      ENNReal.ofReal (∫ u in Ioc 0 θ, lowerQuantile (μ.map Y) u) := by
  have hp : IsProbabilityMeasure (μ.map Y) := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).mpr inferInstance
  have hn : ∀ᵐ y ∂μ.map Y, 0 ≤ y :=
    (ae_map_iff hY.aemeasurable measurableSet_Ici).mpr (Eventually.of_forall hY0)
  rw [ThresholdSelectors.primalTrim_eq_populationTrim hY hY0 hθ]
  congr 1
  rw [← populationTrim_eq_lowerQuantile_integral (μ.map Y) hn θ hθ]
  unfold populationTrim
  congr 1
  ext z
  simp only [id_eq]
  have he (t : ℝ) : (∫ x, max (t - x) 0 ∂μ.map Y) = ∫ ω, max (t - Y ω) 0 ∂μ :=
    integral_map hY.aemeasurable (by fun_prop)
  simp_rw [he]

#print axioms populationTrim_eq_lowerQuantile_integral
#print axioms primalTrim_eq_lowerQuantile_integral
end NLA.IE21.QuantileIntegral
