module

public import NLA.MF05.PaperHolder

@[expose] public section

set_option autoImplicit false
open scoped Topology
open NLA.MF07 Filter
noncomputable section
namespace NLA.MF05.Paper

theorem paper_complexify_spectralNorm {d : ℕ} (A : RealSquare d) :
    NLA.MF07.spectralNorm (complexify A) = realSpectralNorm A := by
  exact complexify_spectralNorm A

theorem paper_complexify_growth {d : ℕ} (M : Set (RealSquare d)) (n : ℕ) :
    familyGrowth (complexify '' M) n = realFamilyGrowth M n := by
  exact complexify_growth M n

theorem paper_complexify_radius {d : ℕ} (M : Set (RealSquare d)) :
    jointSpectralRadius (complexify '' M) = realRadius M := by
  exact complexify_radius M

theorem paper_complexify_hausdorff {d : ℕ} (M N : Set (RealSquare d)) :
    canonicalHausdorff (complexify '' M) (complexify '' N) = realHausdorff M N := by
  exact complexify_hausdorff M N

theorem paper_real_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (RealSquare d))
    (hM : IsCompact M) (hne : M.Nonempty) :
    Tendsto (realRootGrowth M) atTop (𝓝 (realRadius M)) := by
  exact real_root_limit hd M hM hne

theorem paper_complex_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) :
    Tendsto (rootGrowth M) atTop (𝓝 (jointSpectralRadius M)) := by
  exact complex_root_limit hd M hM hne

theorem paper_complex_uniform_holder {d : ℕ} (hd : 1 ≤ d) (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hNL : InNormBall N L) :
    |jointSpectralRadius M - jointSpectralRadius N| ≤
      (d : ℝ)*(2*(d : ℝ)+1) * Real.rpow L (1-1/(d : ℝ)) *
        Real.rpow (canonicalHausdorff M N) (1/(d : ℝ)) := by
  exact complex_uniform_holder hd M N hM hneM hN hneN L hL hML hNL

theorem paper_complex_scalar_holder (M N : Set (Square 1))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hNL : InNormBall N L) :
    |jointSpectralRadius M - jointSpectralRadius N| ≤ canonicalHausdorff M N := by
  exact complex_scalar_holder M N hM hneM hN hneN L hL hML hNL

theorem paper_real_uniform_holder {d : ℕ} (hd : 1 ≤ d) (M N : Set (RealSquare d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L)
    (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (hNL : ∀ A ∈ N, realSpectralNorm A ≤ L) :
    |realRadius M - realRadius N| ≤
      (d : ℝ)*(2*(d : ℝ)+1) * Real.rpow L (1-1/(d : ℝ)) *
        Real.rpow (realHausdorff M N) (1/(d : ℝ)) := by
  exact real_uniform_holder hd M N hM hneM hN hneN L hL hML hNL

theorem paper_real_scalar_holder (M N : Set (RealSquare 1))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L)
    (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (hNL : ∀ A ∈ N, realSpectralNorm A ≤ L) :
    |realRadius M - realRadius N| ≤ realHausdorff M N := by
  exact real_scalar_holder M N hM hneM hN hneN L hL hML hNL

theorem paper_complex_zero_ball {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hML : InNormBall M 0) :
    jointSpectralRadius M = 0 := by
  exact complex_zero_ball hd M hM hne hML

theorem paper_real_zero_ball {d : ℕ} (hd : 1 ≤ d) (M : Set (RealSquare d))
    (hM : IsCompact M) (hne : M.Nonempty) (hML : ∀ A ∈ M, realSpectralNorm A ≤ 0) :
    realRadius M = 0 := by
  exact real_zero_ball hd M hM hne hML

#print axioms paper_complexify_spectralNorm
#print axioms paper_complexify_growth
#print axioms paper_complexify_radius
#print axioms paper_complexify_hausdorff
#print axioms paper_real_root_limit
#print axioms paper_complex_root_limit
#print axioms paper_complex_uniform_holder
#print axioms paper_complex_scalar_holder
#print axioms paper_real_uniform_holder
#print axioms paper_real_scalar_holder
#print axioms paper_complex_zero_ball
#print axioms paper_real_zero_ball

end NLA.MF05.Paper
