module

public import NLA.MF05.PaperCyclicSimilarity
public import NLA.MF05.PaperSingletonRadius

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NLA.MF05.Paper.Cyclic

theorem singleton_radius_le_of_power_bound {d : ℕ} (hd : 1 ≤ d)
    (A : RealSquare d) (r K : ℝ) (hr : 0 < r) (hK : 0 < K)
    (hb : ∀ k, realSpectralNorm (A^k) ≤ K*r^k) : realRadius {A} ≤ r := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hv := NLA.MF05.eventually_rootGrowth_lt_of_exponential_bound
    (complexify '' {A}) (isCompact_singleton.image continuous_complexify)
    ((Set.singleton_nonempty A).image complexify) K r (r+ε) hK hr (by linarith)
    (fun k => by rw [complexify_growth, singleton_growth]; exact hb k)
  have he : ∀ᶠ k : ℕ in atTop, realRootGrowth {A} k < r+ε := by
    simpa only [complexify_rootGrowth] using hv
  obtain ⟨k, hk, hroot⟩ := ((eventually_ge_atTop (1 : ℕ)).and he).exists
  exact (singleton_radius_le_root A k hk).trans hroot.le

theorem spectralNorm_mul_le {d : ℕ} (A B : RealSquare d) :
    realSpectralNorm (A*B) ≤ realSpectralNorm A * realSpectralNorm B := by
  simpa only [realSpectralNorm, map_mul] using
    norm_mul_le (Matrix.toEuclideanCLM (𝕜 := ℝ) A) (Matrix.toEuclideanCLM (𝕜 := ℝ) B)

theorem perturbation_power_bound (n k : ℕ) (r : ℝ) (hr : 0 < r) :
    realSpectralNorm (perturbation n (r^(n+1)) ^ k) ≤
      (realSpectralNorm (scaling n r) * realSpectralNorm (unscaling n r) + 1) * r^k := by
  have hs : realSpectralNorm (r • perturbation n 1) ≤ r := by
    have hn := perturbation_norm_le_one n 1 (by norm_num)
    simp only [realSpectralNorm, map_smul, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr] at hn ⊢
    nlinarith
  have hp : realSpectralNorm ((r • perturbation n 1)^k) ≤ r^k := by
    calc
      _ ≤ realSpectralNorm (r • perturbation n 1)^k := by
        simpa only [realSpectralNorm, map_pow] using
          norm_pow_le (Matrix.toEuclideanCLM (𝕜 := ℝ) (r • perturbation n 1)) k
      _ ≤ r^k := pow_le_pow_left₀ (norm_nonneg _) hs _
  rw [perturbation_power_conjugate n k r hr.ne']
  calc
    _ ≤ (realSpectralNorm (scaling n r) *
        realSpectralNorm ((r • perturbation n 1)^k)) * realSpectralNorm (unscaling n r) :=
      (spectralNorm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (spectralNorm_mul_le _ _) (norm_nonneg _))
    _ ≤ (realSpectralNorm (scaling n r) * r^k) * realSpectralNorm (unscaling n r) := by
      gcongr <;> exact norm_nonneg _
    _ ≤ _ := by
      have hpow := pow_nonneg hr.le k
      nlinarith

theorem perturbation_radius (n : ℕ) (r : ℝ) (hr : 0 < r) :
    realRadius {perturbation n (r^(n+1))} = r := by
  apply le_antisymm _ (perturbation_radius_lower n r hr.le)
  apply singleton_radius_le_of_power_bound (by omega) _ r
    (realSpectralNorm (scaling n r) * realSpectralNorm (unscaling n r) + 1) hr
  · have h1 : 0 ≤ realSpectralNorm (scaling n r) := norm_nonneg _
    have h2 : 0 ≤ realSpectralNorm (unscaling n r) := norm_nonneg _
    positivity
  · exact fun k => perturbation_power_bound n k r hr

#print axioms perturbation_radius
end NLA.MF05.Paper.Cyclic
