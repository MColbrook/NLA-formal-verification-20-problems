module

public import NLA.RA02.PaperResidualEquivalence
public import NLA.RA02.PaperInterpolationSelected
public import NLA.RA02.PaperInterpolationMissing

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter Asymptotics
namespace NLA.RA02.Paper

theorem interpolation_eventually_positive {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < interpolationSquaredNorm hs rows t := by
  filter_upwards [interpolation_norm_lower_bound hs rows] with t ht
  linarith

theorem trace_asymptotic_ratio {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    Tendsto (fun t => paperTrace rows t / (epsilon n t^s * interpolationSquaredNorm hs rows t))
      (𝓝[>] 0) (𝓝 1) := by
  have hn : ∀ᶠ t : ℝ in 𝓝[>] 0, interpolationSquaredNorm hs rows t ≠ 0 :=
    (interpolation_eventually_positive hs rows).mono (fun _ ht => ne_of_gt ht)
  have hh := (isEquivalent_iff_tendsto_one hn).mp (trace_equivalent hs rows)
  change Tendsto (fun t => (paperTrace rows t / epsilon n t^s) / interpolationSquaredNorm hs rows t) _ _ at hh
  simpa only [Pi.div_apply, div_div] using hh

theorem frobenius_asymptotic_ratio {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) :
    Tendsto (fun t => paperFrobeniusSquared rows cols t /
      (epsilon n t^(2*s) * interpolationSquaredNorm hs rows t * interpolationSquaredNorm hs cols t))
      (𝓝[>] 0) (𝓝 1) := by
  have hn : ∀ᶠ t : ℝ in 𝓝[>] 0,
      interpolationSquaredNorm hs rows t * interpolationSquaredNorm hs cols t ≠ 0 := by
    filter_upwards [interpolation_eventually_positive hs rows, interpolation_eventually_positive hs cols]
      with t hr hc
    exact mul_ne_zero (ne_of_gt hr) (ne_of_gt hc)
  have hh := (isEquivalent_iff_tendsto_one hn).mp (frobenius_equivalent hs rows cols)
  change Tendsto (fun t => (paperFrobeniusSquared rows cols t / epsilon n t^(2*s)) /
    (interpolationSquaredNorm hs rows t * interpolationSquaredNorm hs cols t)) _ _ at hh
  simpa only [Pi.div_apply, div_div, mul_assoc] using hh

theorem reciprocal_ratio_transfer (a b c : ℝ → ℝ) (L : ℝ)
    (ha : Tendsto (fun t => a t / (b t*c t)) (𝓝[>] 0) (𝓝 1))
    (hc : Tendsto (fun t => (c t)⁻¹) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun t => b t/a t) (𝓝[>] 0) (𝓝 L) := by
  have hh := hc.div ha one_ne_zero
  simp only [div_one] at hh
  apply hh.congr'
  have hn := ha.eventually (eventually_ne_nhds one_ne_zero)
  filter_upwards [hn] with t ht
  have hna := (div_ne_zero_iff.mp ht).1
  have hnc := (mul_ne_zero_iff.mp (div_ne_zero_iff.mp ht).2).2
  simp only [Pi.div_apply]
  field_simp

theorem interpolation_indicator_limit {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    Tendsto (fun t => (interpolationSquaredNorm hs rows t)⁻¹) (𝓝[>] 0)
      (𝓝 (if (⟨s,hs⟩ : Fin n) ∉ Set.range rows then 1 else 0)) := by
  by_cases hm : (⟨s,hs⟩ : Fin n) ∈ Set.range rows
  · rw [if_neg (not_not.mpr hm)]
    exact interpolation_selected_reciprocal_limit hs rows hm
  · rw [if_pos hm]
    exact interpolation_missing_reciprocal_limit hs rows hm

theorem trace_indicator_limit {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) :
    Tendsto (fun t => epsilon n t^s / paperTrace rows t) (𝓝[>] 0)
      (𝓝 (if (⟨s,hs⟩ : Fin n) ∉ Set.range rows then 1 else 0)) :=
  reciprocal_ratio_transfer _ _ _ _ (trace_asymptotic_ratio hs rows) (interpolation_indicator_limit hs rows)

theorem frobenius_indicator_limit {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) :
    Tendsto (fun t => epsilon n t^(2*s) / paperFrobeniusSquared rows cols t) (𝓝[>] 0)
      (𝓝 ((if (⟨s,hs⟩ : Fin n) ∉ Set.range rows then 1 else 0) *
        (if (⟨s,hs⟩ : Fin n) ∉ Set.range cols then 1 else 0))) := by
  have hc : Tendsto (fun t => (interpolationSquaredNorm hs rows t * interpolationSquaredNorm hs cols t)⁻¹)
      (𝓝[>] 0) (𝓝 ((if (⟨s,hs⟩ : Fin n) ∉ Set.range rows then 1 else 0) *
        (if (⟨s,hs⟩ : Fin n) ∉ Set.range cols then 1 else 0))) := by
    simpa only [mul_inv_rev, mul_comm] using
      (interpolation_indicator_limit hs rows).mul (interpolation_indicator_limit hs cols)
  apply reciprocal_ratio_transfer _ _ _ _ _ hc
  simpa only [mul_assoc] using frobenius_asymptotic_ratio hs rows cols

#print axioms frobenius_indicator_limit
end NLA.RA02.Paper
