module

public import NLA.IE21.QuantileIntegral.Definitions
public import NLA.IE21.ThresholdSelectors.Quantile
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace NLA.IE21.QuantileIntegral

theorem quantile_set_nonempty (μ : Measure ℝ) {u : ℝ} (hu : u < 1) :
    {x | u ≤ cdf μ x}.Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hu)).exists
  exact ⟨x, hx.le⟩

theorem quantile_set_bddBelow (μ : Measure ℝ) {u : ℝ} (hu : 0 < u) :
    BddBelow {x | u ≤ cdf μ x} := by
  obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hu)).exists
  refine ⟨a, ?_⟩
  intro x hx
  by_contra hn
  have hxa : x ≤ a := (lt_of_not_ge hn).le
  have := (monotone_cdf μ) hxa
  change u ≤ cdf μ x at hx
  linarith

theorem le_cdf_lowerQuantile (μ : Measure ℝ) {u : ℝ} (hu : 0 < u ∧ u < 1) :
    u ≤ cdf μ (lowerQuantile μ u) := by
  have hright (x : ℝ) (hx : lowerQuantile μ u < x) : u ≤ cdf μ x := by
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt (quantile_set_nonempty μ hu.2) hx
    exact le_trans hy ((monotone_cdf μ) hyx.le)
  have ht : Tendsto (cdf μ) (𝓝[>] (lowerQuantile μ u)) (𝓝 (cdf μ (lowerQuantile μ u))) :=
    ((cdf μ).right_continuous _).mono_left
      (nhdsWithin_mono _ (show Ioi (lowerQuantile μ u) ⊆ Ici (lowerQuantile μ u)
        from fun x hx => (show lowerQuantile μ u < x from hx).le))
  exact ge_of_tendsto ht (eventually_mem_nhdsWithin.mono fun x hx => hright x hx)

theorem lowerQuantile_le_iff (μ : Measure ℝ) {u x : ℝ} (hu : 0 < u ∧ u < 1) :
    lowerQuantile μ u ≤ x ↔ u ≤ cdf μ x := by
  constructor
  · exact fun h => (le_cdf_lowerQuantile μ hu).trans ((monotone_cdf μ) h)
  · exact fun h => csInf_le (quantile_set_bddBelow μ hu.1) h

theorem lowerQuantile_monotoneOn (μ : Measure ℝ) : MonotoneOn (lowerQuantile μ) (Ioo 0 1) := by
  intro u hu v hv huv
  exact (lowerQuantile_le_iff μ hu).mpr (huv.trans (le_cdf_lowerQuantile μ hv))

theorem lowerQuantile_aemeasurable (μ : Measure ℝ) :
    AEMeasurable (lowerQuantile μ) (volume.restrict (Ioo 0 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (lowerQuantile_monotoneOn μ)

theorem lowerQuantile_map (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map (lowerQuantile μ) = μ := by
  have hv : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := by
    constructor
    simp
  have hp : IsProbabilityMeasure ((volume.restrict (Ioo (0 : ℝ) 1)).map (lowerQuantile μ)) :=
    (Measure.isProbabilityMeasure_map_iff (lowerQuantile_aemeasurable μ)).mpr inferInstance
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply_of_aemeasurable (lowerQuantile_aemeasurable μ) measurableSet_Iic,
    Measure.restrict_apply₀]
  · have he : lowerQuantile μ ⁻¹' Iic x ∩ Ioo 0 1 = Ioc 0 (cdf μ x) ∩ Ioo 0 1 := by
      ext u
      simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc, mem_Ioo]
      constructor
      · rintro ⟨hux, hu0, hu1⟩
        exact ⟨⟨hu0, (lowerQuantile_le_iff μ ⟨hu0, hu1⟩).mp hux⟩, hu0, hu1⟩
      · rintro ⟨⟨hu0, hux⟩, _, hu1⟩
        exact ⟨(lowerQuantile_le_iff μ ⟨hu0, hu1⟩).mpr hux, hu0, hu1⟩
    rw [he]
    have heq : (Ioc 0 (cdf μ x) ∩ Ioo 0 1 : Set ℝ) =ᵐ[volume] Ioc 0 (cdf μ x) := by
      filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 1 from volume.ae_ne 1] with u hu
      apply propext
      change ((0 < u ∧ u ≤ cdf μ x) ∧ 0 < u ∧ u < 1) ↔ (0 < u ∧ u ≤ cdf μ x)
      constructor
      · exact And.left
      · intro h
        exact ⟨h, h.1, lt_of_le_of_ne (h.2.trans (cdf_le_one μ x)) hu⟩
    rw [measure_congr heq, Real.volume_Ioc, sub_zero, ofReal_cdf]
  · exact (lowerQuantile_aemeasurable μ).nullMeasurable measurableSet_Iic

#print axioms lowerQuantile_le_iff
#print axioms lowerQuantile_map
end NLA.IE21.QuantileIntegral
