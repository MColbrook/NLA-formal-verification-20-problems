module

public import NLA.MF05.PaperRealFamilies
public import NLA.MF05.PaperScalar
public import NLA.MF05.UniformHolder

@[expose] public section

set_option autoImplicit false
open NLA.MF07
open scoped Topology
open Filter
noncomputable section
namespace NLA.MF05.Paper

theorem complex_root_limit {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) :
    Tendsto (rootGrowth M) atTop (𝓝 (jointSpectralRadius M)) := by
  exact (general_root_limit_semantics hd M hM hne).2.2

theorem complex_uniform_holder {d : ℕ} (hd : 1 ≤ d) (M N : Set (Square d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hNL : InNormBall N L) :
    |jointSpectralRadius M - jointSpectralRadius N| ≤
      (d : ℝ)*(2*(d : ℝ)+1) * Real.rpow L (1-1/(d : ℝ)) *
        Real.rpow (canonicalHausdorff M N) (1/(d : ℝ)) := by
  obtain ⟨_, _, _, he, _, _, _, _, _⟩ := spectral_hausdorff_semantics M N hM hneM hN hneN
  simpa only [holderConstant, he] using
    (uniform_holder_estimate hd M N hM hneM hN hneN L hL hML hNL).2

theorem complex_scalar_holder (M N : Set (Square 1))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (hNL : InNormBall N L) :
    |jointSpectralRadius M - jointSpectralRadius N| ≤ canonicalHausdorff M N := by
  obtain ⟨_, _, _, he, _, _, _, _, _⟩ := spectral_hausdorff_semantics M N hM hneM hN hneN
  simpa only [he] using scalar_holder_coefficient_one M N hM hneM hN hneN L hL hML hNL

theorem complexify_normBall {d : ℕ} (M : Set (RealSquare d)) (L : ℝ)
    (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) : InNormBall (complexify '' M) L := by
  rintro B ⟨A, hA, rfl⟩
  rw [complexify_spectralNorm]
  exact hML A hA

theorem real_uniform_holder {d : ℕ} (hd : 1 ≤ d) (M N : Set (RealSquare d))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L)
    (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (hNL : ∀ A ∈ N, realSpectralNorm A ≤ L) :
    |realRadius M - realRadius N| ≤
      (d : ℝ)*(2*(d : ℝ)+1) * Real.rpow L (1-1/(d : ℝ)) *
        Real.rpow (realHausdorff M N) (1/(d : ℝ)) := by
  have h := complex_uniform_holder hd (complexify '' M) (complexify '' N)
    (hM.image continuous_complexify) (hneM.image complexify)
    (hN.image continuous_complexify) (hneN.image complexify) L hL
    (complexify_normBall M L hML) (complexify_normBall N L hNL)
  simpa only [complexify_radius, complexify_hausdorff] using h

theorem real_scalar_holder (M N : Set (RealSquare 1))
    (hM : IsCompact M) (hneM : M.Nonempty) (hN : IsCompact N) (hneN : N.Nonempty)
    (L : ℝ) (hL : 0 < L)
    (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (hNL : ∀ A ∈ N, realSpectralNorm A ≤ L) :
    |realRadius M - realRadius N| ≤ realHausdorff M N := by
  have h := complex_scalar_holder (complexify '' M) (complexify '' N)
    (hM.image continuous_complexify) (hneM.image complexify)
    (hN.image continuous_complexify) (hneN.image complexify) L hL
    (complexify_normBall M L hML) (complexify_normBall N L hNL)
  simpa only [complexify_radius, complexify_hausdorff] using h

theorem complex_zero_ball {d : ℕ} (hd : 1 ≤ d) (M : Set (Square d))
    (hM : IsCompact M) (hne : M.Nonempty) (hML : InNormBall M 0) :
    jointSpectralRadius M = 0 := by
  obtain ⟨hl, hu⟩ := jointSpectralRadius_bounds_of_inNormBall hd M hM hne 0 hML
  exact le_antisymm hu hl

theorem real_zero_ball {d : ℕ} (hd : 1 ≤ d) (M : Set (RealSquare d))
    (hM : IsCompact M) (hne : M.Nonempty) (hML : ∀ A ∈ M, realSpectralNorm A ≤ 0) :
    realRadius M = 0 := by
  have h := complex_zero_ball hd (complexify '' M) (hM.image continuous_complexify)
    (hne.image complexify) (complexify_normBall M 0 hML)
  simpa only [complexify_radius] using h

#print axioms complex_uniform_holder
#print axioms complex_scalar_holder
#print axioms real_uniform_holder
#print axioms real_scalar_holder
#print axioms complex_zero_ball
#print axioms real_zero_ball
end NLA.MF05.Paper
