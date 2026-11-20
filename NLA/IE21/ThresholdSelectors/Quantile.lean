module

public import Mathlib.Probability.CDF
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace NLA.IE21.ThresholdSelectors

/-- Every probability distribution admits a threshold with the requested mass
between its open and closed lower tails, including distributions with atoms. -/
theorem exists_quantile_bracket (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    ∃ q : ℝ, μ.real (Iio q) ≤ θ ∧ θ ≤ μ.real (Iic q) := by
  let S : Set ℝ := {x | θ ≤ cdf μ x}
  have hS : S.Nonempty := by
    obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds hθ.2)).exists
    exact ⟨x, hx.le⟩
  have hb : BddBelow S := by
    obtain ⟨a, ha⟩ := ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hθ.1)).exists
    refine ⟨a, ?_⟩
    intro x hx
    by_contra hax
    have hx' : θ ≤ cdf μ x := hx
    have := (monotone_cdf μ) (le_of_lt (lt_of_not_ge hax))
    linarith
  let q := sInf S
  have hleft (x : ℝ) (hx : x < q) : cdf μ x < θ := by
    by_contra hc
    have hxs : x ∈ S := le_of_not_gt hc
    exact (not_le_of_gt hx) (csInf_le hb hxs)
  have hright (x : ℝ) (hx : q < x) : θ ≤ cdf μ x := by
    obtain ⟨y, hy, hyx⟩ := exists_lt_of_csInf_lt hS hx
    exact le_trans hy ((monotone_cdf μ) hyx.le)
  have hq : θ ≤ cdf μ q := by
    have ht : Tendsto (cdf μ) (𝓝[>] q) (𝓝 (cdf μ q)) :=
      ((cdf μ).right_continuous q).mono_left
        (nhdsWithin_mono q (show Ioi q ⊆ Ici q from fun x hx => (show q < x from hx).le))
    exact ge_of_tendsto ht (eventually_mem_nhdsWithin.mono fun x hx => hright x hx)
  have hl : Function.leftLim (cdf μ) q ≤ θ := by
    exact le_of_tendsto ((monotone_cdf μ).tendsto_leftLim q)
      (eventually_mem_nhdsWithin.mono fun x hx => (hleft x hx).le)
  have hl0 : 0 ≤ Function.leftLim (cdf μ) q := by
    exact ge_of_tendsto ((monotone_cdf μ).tendsto_leftLim q)
      (Eventually.of_forall (cdf_nonneg μ))
  have heq : μ.real (Iio q) = Function.leftLim (cdf μ) q := by
    unfold Measure.real
    have hm := (cdf μ).measure_Iio (tendsto_cdf_atBot μ) q
    rw [measure_cdf, sub_zero] at hm
    rw [hm, ENNReal.toReal_ofReal hl0]
  exact ⟨q, heq ▸ hl, (cdf_eq_real μ q) ▸ hq⟩

#print axioms exists_quantile_bracket

end NLA.IE21.ThresholdSelectors
