module

public import NLA.MF05.PaperEccentricity
public import NLA.MF05.PaperDamping

@[expose] public section

set_option autoImplicit false
open scoped Topology Matrix.Norms.L2Operator
open NLA.MF07 Filter
noncomputable section
namespace NLA.MF05.Paper

theorem paper_complex_bounded_comparison_norm {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (ε : ℝ) (hε : 0 < ε) (hεL : ε ≤ 2*(d : ℝ)^2*L) :
    ∃ p : EuclideanVector d → ℝ, IsComplexNorm p ∧
      (∀ x, ‖x‖ ≤ p x ∧ p x ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1)*‖x‖) ∧
      (∀ A ∈ M, ∀ x, p (applyMatrix A x) ≤ (jointSpectralRadius M+ε)*p x) := by
  exact complex_bounded_comparison_norm hd M hM hne L hL hML ε hε hεL

theorem paper_real_bounded_comparison_norm {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (ε : ℝ) (hε : 0 < ε) (hεL : ε ≤ 2*(d : ℝ)^2*L) :
    ∃ p : RealVector d → ℝ, IsRealNorm p ∧
      (∀ x, ‖x‖ ≤ p x ∧ p x ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1)*‖x‖) ∧
      (∀ A ∈ M, ∀ x, p (Matrix.toEuclideanCLM (𝕜:=ℝ) A x) ≤ (realRadius M+ε)*p x) := by
  exact real_bounded_comparison_norm hd M hM hne L hL hML ε hε hεL

theorem paper_complex_bounded_eccentricity {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (ε : ℝ) (hε : 0 < ε) (hεL : ε ≤ 2*(d : ℝ)^2*L) :
    ∃ p : EuclideanVector d → ℝ, IsComplexNorm p ∧
      sSup ((fun A => inducedNorm p (applyMatrix A)) '' M) ≤ jointSpectralRadius M+ε ∧
      eccentricity p ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1) := by
  exact complex_bounded_eccentricity hd M hM hne L hL hML ε hε hεL

theorem paper_real_bounded_eccentricity {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (ε : ℝ) (hε : 0 < ε) (hεL : ε ≤ 2*(d : ℝ)^2*L) :
    ∃ p : RealVector d → ℝ, IsRealNorm p ∧
      sSup ((fun A => inducedNorm p (Matrix.toEuclideanCLM (𝕜:=ℝ) A)) '' M) ≤ realRadius M+ε ∧
      eccentricity p ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1) := by
  exact real_bounded_eccentricity hd M hM hne L hL hML ε hε hεL

theorem paper_complex_block_damping {d b : ℕ} (block : Fin d → Fin b) (hblock : Monotone block)
    (h : Fin b → ℝ) (hh : Antitone h) (hpos : ∀ i, 0 < h i)
    (X : Square d) (hX : ∀ i j, block i < block j → X i j = 0) :
    spectralNorm (diagonalWeights (h ∘ block) * X * (diagonalWeights (h ∘ block))⁻¹) ≤
      spectralNorm X := by
  exact complex_block_damping block hblock h hh hpos X hX

theorem paper_real_block_damping {d b : ℕ} (block : Fin d → Fin b) (hblock : Monotone block)
    (h : Fin b → ℝ) (hh : Antitone h) (hpos : ∀ i, 0 < h i)
    (X : RealSquare d) (hX : ∀ i j, block i < block j → X i j = 0) :
    realSpectralNorm (Matrix.diagonal (h ∘ block) * X *
      (Matrix.diagonal (h ∘ block))⁻¹) ≤ realSpectralNorm X := by
  exact real_block_damping block hblock h hh hpos X hX

#print axioms paper_complex_bounded_comparison_norm
#print axioms paper_real_bounded_comparison_norm
#print axioms paper_complex_bounded_eccentricity
#print axioms paper_real_bounded_eccentricity
#print axioms paper_complex_block_damping
#print axioms paper_real_block_damping

end NLA.MF05.Paper
