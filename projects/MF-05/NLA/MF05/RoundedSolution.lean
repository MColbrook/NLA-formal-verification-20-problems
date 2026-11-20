module

public import NLA.MF05.PaperRounded

@[expose] public section

set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
open NLA.MF07
noncomputable section
namespace NLA.MF05.Paper

theorem paper_complex_rounded_extremal_norm {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L) (a : ℝ) (ha : jointSpectralRadius M < a) :
    ∃ (Q : Square d) (σ : Fin d → ℝ) (w : EuclideanVector d → ℝ),
      Q.conjTranspose*Q = 1 ∧ Q*Q.conjTranspose = 1 ∧
      Antitone σ ∧ (∀ i, 0 < σ i) ∧ IsComplexNorm w ∧
      (∀ z, ‖z‖ ≤ w z ∧ w z ≤ (d : ℝ)*‖z‖) ∧
      (∀ A ∈ M, inducedNorm w (applyMatrix (complexRotated Q σ A)) ≤ a) ∧
      ∀ A ∈ M, ∀ i j, ‖complexRotated Q σ A i j‖ ≤ L*σ j/σ i := by
  exact complex_rounded_extremal_norm hd M hM hne L hL hML a ha

theorem paper_real_rounded_extremal_norm {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L) (a : ℝ) (ha : realRadius M < a) :
    ∃ (Q : RealSquare d) (σ : Fin d → ℝ) (w : RealVector d → ℝ),
      Q.transpose*Q = 1 ∧ Q*Q.transpose = 1 ∧
      Antitone σ ∧ (∀ i, 0 < σ i) ∧ IsRealNorm w ∧
      (∀ z, ‖z‖ ≤ w z ∧ w z ≤ (d : ℝ)*‖z‖) ∧
      (∀ A ∈ M, inducedNorm w (Matrix.toEuclideanCLM (𝕜:=ℝ) (realRotated Q σ A)) ≤ a) ∧
      ∀ A ∈ M, ∀ i j, ‖realRotated Q σ A i j‖ ≤ L*σ j/σ i := by
  exact real_rounded_extremal_norm hd M hM hne L hL hML a ha

#print axioms paper_complex_rounded_extremal_norm
#print axioms paper_real_rounded_extremal_norm
end NLA.MF05.Paper
