module

public import NLA.RA02.PaperSpectralFactorization

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NLA.RA02.Paper

theorem spectral_scale_det (s : ℕ) (e : ℝ) :
    (Matrix.diagonal (fun i : Fin s => e^i.val)).det = e^(s*(s-1)/2) := by
  rw [Matrix.det_diagonal, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun i => i) s, Finset.sum_range_id]

theorem spectral_minor_ratio {n s : ℕ} (hs : s < n) (rows cols : Fin s ↪ Fin n) :
    Tendsto (fun t : ℝ => ((sharpFamily n t).submatrix rows cols).det /
      (epsilon n t^(s*(s-1)/2) * (prefixMatrix hs.le rows t).det * (prefixMatrix hs.le cols t).det))
      (𝓝[>] 0) (𝓝 1) := by
  apply (spectralCorrection_det_limit hs rows cols).congr'
  filter_upwards [prefix_eventually_nonsingular hs.le rows,
    prefix_eventually_nonsingular hs.le cols, self_mem_nhdsWithin] with t hu hv ht
  have ht' : t ≠ 0 := ne_of_gt (show 0 < t from ht)
  have he : epsilon n t ≠ 0 := pow_ne_zero _ ht'
  have huu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hu)
  have hvu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hv)
  rw [spectral_factorization hs rows cols ht' huu hvu]
  simp only [Matrix.det_mul, Matrix.det_transpose, spectral_scale_det]
  field_simp
  <;> ring

theorem spectral_minor_eventually_nonzero_lt {n s : ℕ} (hs : s < n)
    (rows cols : Fin s ↪ Fin n) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ((sharpFamily n t).submatrix rows cols).det ≠ 0 := by
  have he := (spectral_minor_ratio hs rows cols).eventually (eventually_ne_nhds one_ne_zero)
  filter_upwards [he] with t ht
  exact (div_ne_zero_iff.mp ht).1

theorem full_minor_nonzero (n : ℕ) (rows cols : Fin n ↪ Fin n) {t : ℝ} (ht : 0 < t) :
    ((sharpFamily n t).submatrix rows cols).det ≠ 0 := by
  let er : Fin n ≃ Fin n := Equiv.ofBijective rows
    ⟨rows.injective, Finite.surjective_of_injective rows.injective⟩
  let ec : Fin n ≃ Fin n := Equiv.ofBijective cols
    ⟨cols.injective, Finite.surjective_of_injective cols.injective⟩
  have ha := Matrix.abs_det_submatrix_equiv_equiv er ec (sharpFamily n t)
  have hn : (sharpFamily n t).det ≠ 0 := by
    rw [sharpFamily_det]
    exact pow_ne_zero _ (pow_ne_zero _ (ne_of_gt ht))
  intro hz
  change |((sharpFamily n t).submatrix rows cols).det| = |(sharpFamily n t).det| at ha
  rw [hz, abs_zero] at ha
  exact hn (abs_eq_zero.mp ha.symm)

theorem spectral_minor_eventually_nonzero {n s : ℕ} (hs : s ≤ n)
    (rows cols : Fin s ↪ Fin n) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ((sharpFamily n t).submatrix rows cols).det ≠ 0 := by
  rcases hs.eq_or_lt with he | he
  · subst n
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact full_minor_nonzero s rows cols ht
  · exact spectral_minor_eventually_nonzero_lt he rows cols

theorem all_minors_eventually_nonzero (n : ℕ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ s : Fin (n+1), ∀ rows cols : Fin s.val ↪ Fin n,
      ((sharpFamily n t).submatrix rows cols).det ≠ 0 := by
  apply Filter.eventually_all.mpr
  intro s
  apply Filter.eventually_all.mpr
  intro rows
  apply Filter.eventually_all.mpr
  intro cols
  exact spectral_minor_eventually_nonzero (by omega) rows cols

#print axioms spectral_minor_ratio
end NLA.RA02.Paper
