module

public import NLA.RA02.PaperResidualBorder
public import NLA.RA02.PaperAllSpectralRatio

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem triangular_exponent_succ (s : ℕ) :
    (s+1)*((s+1)-1)/2 = s*(s-1)/2+s := by
  have h := Finset.sum_range_succ (fun i : ℕ => i) s
  simpa only [Finset.sum_range_id] using h

theorem residual_entry_ratio {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n)
    (i j : Fin n) (hi : i ∉ Set.range rows) (hj : j ∉ Set.range cols) :
    Tendsto (fun t : ℝ => interpolatoryResidual (sharpFamily n t) rows cols i j /
      (epsilon n t^s * interpolationResidual hs rows t i * interpolationResidual hs cols t j))
      (𝓝[>] 0) (𝓝 1) := by
  have hh := (spectral_minor_ratio_all (Nat.succ_le_of_lt hs)
    (appendEmbedding rows i hi) (appendEmbedding cols j hj)).div
    (spectral_minor_ratio_all hs.le rows cols) one_ne_zero
  simp only [div_self one_ne_zero] at hh
  apply hh.congr'
  filter_upwards [spectral_minor_eventually_nonzero hs.le rows cols,
    prefix_eventually_nonsingular hs.le rows, prefix_eventually_nonsingular hs.le cols,
    interpolation_component_eventually_nonzero hs rows i hi,
    interpolation_component_eventually_nonzero hs cols j hj,
    self_mem_nhdsWithin] with t ha hr hc hwi hwj ht
  have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ha)
  have hrunit := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hr)
  have hcunit := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hc)
  have he : epsilon n t ≠ 0 := pow_ne_zero _ (ne_of_gt (show 0 < t from ht))
  simp only [Pi.div_apply]
  erw [residual_bordered_determinant _ rows cols i j hi hj hunit,
    prefix_bordered_determinant hs rows i hi t hrunit,
    prefix_bordered_determinant hs cols j hj t hcunit,
    triangular_exponent_succ, pow_add]
  field_simp
  <;> ring

#print axioms residual_entry_ratio
end NLA.RA02.Paper
