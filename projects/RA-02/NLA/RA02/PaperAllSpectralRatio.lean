module

public import NLA.RA02.PaperSpectralConclusions

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NLA.RA02.Paper

theorem full_spectral_tail_zero (n : ℕ) (rows cols : Fin n ↪ Fin n) (t : ℝ) :
    scaledSpectralTail rows cols t = 0 := by
  ext i j
  apply Finset.sum_eq_zero
  intro k _
  simp only [if_neg (Nat.not_le.mpr k.isLt)]

theorem spectral_minor_ratio_all {n s : ℕ} (hs : s ≤ n) (rows cols : Fin s ↪ Fin n) :
    Tendsto (fun t : ℝ => ((sharpFamily n t).submatrix rows cols).det /
      (epsilon n t^(s*(s-1)/2) * (prefixMatrix hs rows t).det * (prefixMatrix hs cols t).det))
      (𝓝[>] 0) (𝓝 1) := by
  rcases hs.eq_or_lt with he | he
  · subst n
    apply tendsto_const_nhds.congr'
    filter_upwards [prefix_eventually_nonsingular hs rows, prefix_eventually_nonsingular hs cols,
      self_mem_nhdsWithin] with t hr hc ht
    have ht' : t ≠ 0 := ne_of_gt (show 0 < t from ht)
    have he : epsilon s t ≠ 0 := pow_ne_zero _ ht'
    rw [spectral_split hs rows cols, full_spectral_tail_zero, smul_zero, add_zero]
    simp only [Matrix.det_mul, Matrix.det_transpose, spectral_scale_det]
    field_simp
  · exact spectral_minor_ratio he rows cols

#print axioms spectral_minor_ratio_all
end NLA.RA02.Paper
