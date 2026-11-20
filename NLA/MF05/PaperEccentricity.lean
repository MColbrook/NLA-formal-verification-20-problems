module

public import NLA.MF05.PaperNormBounds

@[expose] public section

set_option autoImplicit false
open NLA.MF07
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MF05.Paper

theorem complex_bounded_eccentricity {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (ε : ℝ) (hε : 0 < ε) (hεL : ε ≤ 2*(d : ℝ)^2*L) :
    ∃ p : EuclideanVector d → ℝ, IsComplexNorm p ∧
      sSup ((fun A => inducedNorm p (applyMatrix A)) '' M) ≤ jointSpectralRadius M+ε ∧
      eccentricity p ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1) := by
  obtain ⟨p, hp, hb, hg⟩ := complex_bounded_comparison_norm hd M hM hne L hL hML ε hε hεL
  let e : EuclideanVector d := PiLp.single 2 (⟨0, by omega⟩ : Fin d) (1 : ℂ)
  have he : ‖e‖ = 1 := by simp [e]
  have he0 : e ≠ 0 := by intro h; simpa [h] using he
  refine ⟨p, hp, ?_, eccentricity_le p _ hb e he⟩
  apply csSup_le (hne.image _)
  rintro r ⟨A, hA, rfl⟩
  exact inducedNorm_le p (applyMatrix A) (fun x => (hb x).1) _ (hg A hA) e he0

theorem real_bounded_eccentricity {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (ε : ℝ) (hε : 0 < ε) (hεL : ε ≤ 2*(d : ℝ)^2*L) :
    ∃ p : RealVector d → ℝ, IsRealNorm p ∧
      sSup ((fun A => inducedNorm p (Matrix.toEuclideanCLM (𝕜:=ℝ) A)) '' M) ≤ realRadius M+ε ∧
      eccentricity p ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1) := by
  obtain ⟨p, hp, hb, hg⟩ := real_bounded_comparison_norm hd M hM hne L hL hML ε hε hεL
  let e : RealVector d := PiLp.single 2 (⟨0, by omega⟩ : Fin d) (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have he0 : e ≠ 0 := by intro h; simpa [h] using he
  refine ⟨p, hp, ?_, eccentricity_le p _ hb e he⟩
  apply csSup_le (hne.image _)
  rintro r ⟨A, hA, rfl⟩
  exact inducedNorm_le p (Matrix.toEuclideanCLM (𝕜:=ℝ) A) (fun x => (hb x).1) _ (hg A hA) e he0

#print axioms complex_bounded_eccentricity
#print axioms real_bounded_eccentricity
end NLA.MF05.Paper
