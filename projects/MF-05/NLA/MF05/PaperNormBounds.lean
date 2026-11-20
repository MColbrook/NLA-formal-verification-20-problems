module

public import NLA.MF05.PaperNormDefinitions
public import NLA.MF05.PaperGrowthFinal

@[expose] public section

set_option autoImplicit false
open NLA.MF07
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace NLA.MF05.Paper

lemma inducedNorm_le {E : Type*} [NormedAddCommGroup E] (p : E → ℝ) (f : E → E)
    (hpos : ∀ x, ‖x‖ ≤ p x) (h : ℝ) (hf : ∀ x, p (f x) ≤ h*p x)
    (e : E) (he : e ≠ 0) : inducedNorm p f ≤ h := by
  unfold inducedNorm
  have hne : ({r : ℝ | ∃ x : E, x ≠ 0 ∧ r = p (f x)/p x}).Nonempty :=
    ⟨p (f e)/p e, e, he, rfl⟩
  apply csSup_le hne
  rintro r ⟨x, hx, rfl⟩
  exact (div_le_iff₀ ((norm_pos_iff.mpr hx).trans_le (hpos x))).mpr (hf x)

lemma eccentricity_le {E : Type*} [NormedAddCommGroup E] (p : E → ℝ) (C : ℝ)
    (hb : ∀ x, ‖x‖ ≤ p x ∧ p x ≤ C*‖x‖) (e : E) (he : ‖e‖ = 1) :
    eccentricity p ≤ C := by
  let S := p '' {x : E | ‖x‖ = 1}
  have hne : S.Nonempty := ⟨p e, e, he, rfl⟩
  have hlo : ∀ r ∈ S, (1 : ℝ) ≤ r := by
    rintro r ⟨x, hx, rfl⟩
    change ‖x‖ = 1 at hx
    simpa only [hx] using (hb x).1
  have hup : ∀ r ∈ S, r ≤ C := by
    rintro r ⟨x, hx, rfl⟩
    change ‖x‖ = 1 at hx
    simpa only [hx, mul_one] using (hb x).2
  have hi : 1 ≤ sInf S := le_csInf hne hlo
  have hs : sSup S ≤ C := csSup_le hne hup
  have hC : 0 ≤ C := by
    have h1 := hlo (p e) ⟨e, he, rfl⟩
    have h2 := hup (p e) ⟨e, he, rfl⟩
    linarith
  change sSup S/sInf S ≤ C
  apply (div_le_iff₀ (by linarith : 0 < sInf S)).mpr
  exact hs.trans (le_mul_of_one_le_right hC hi)

theorem complex_bounded_comparison_norm {d : ℕ} (hd : 1 ≤ d)
    (M : Set (Square d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : InNormBall M L)
    (ε : ℝ) (hε : 0 < ε) (hεL : ε ≤ 2*(d : ℝ)^2*L) :
    ∃ p : EuclideanVector d → ℝ, IsComplexNorm p ∧
      (∀ x, ‖x‖ ≤ p x ∧ p x ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1)*‖x‖) ∧
      (∀ A ∈ M, ∀ x, p (applyMatrix A x) ≤ (jointSpectralRadius M+ε)*p x) := by
  let s := 2*(d : ℝ)^2*L/ε
  have hs : 1 ≤ s := (one_le_div hε).mpr hεL
  obtain ⟨_, hp, hb, hg⟩ := controlled_comparison_norm hd (closure M)
    hM.isCompact_closure (hne.mono subset_closure) L s hL (complex_closure_normBall M L hML) hs
  have hnum : 2*(d : ℝ)^2*L ≠ 0 := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    positivity
  have he : comparisonRate d (closure M) L s = jointSpectralRadius M+ε := by
    rw [comparisonRate, complex_closure_radius M hM hne]
    dsimp [s]
    field_simp
  refine ⟨comparisonNorm d (closure M) L s, hp, hb, ?_⟩
  intro A hA x
  simpa only [he] using hg A (subset_closure hA) x

theorem real_bounded_comparison_norm {d : ℕ} (hd : 1 ≤ d)
    (M : Set (RealSquare d)) (hM : Bornology.IsBounded M) (hne : M.Nonempty)
    (L : ℝ) (hL : 0 < L) (hML : ∀ A ∈ M, realSpectralNorm A ≤ L)
    (ε : ℝ) (hε : 0 < ε) (hεL : ε ≤ 2*(d : ℝ)^2*L) :
    ∃ p : RealVector d → ℝ, IsRealNorm p ∧
      (∀ x, ‖x‖ ≤ p x ∧ p x ≤ (d : ℝ)*(2*(d : ℝ)^2*L/ε)^(d-1)*‖x‖) ∧
      (∀ A ∈ M, ∀ x, p (Matrix.toEuclideanCLM (𝕜:=ℝ) A x) ≤ (realRadius M+ε)*p x) := by
  obtain ⟨p, hp, hb, hg⟩ := complex_bounded_comparison_norm hd (complexify '' M)
    (complexify_bounded M hM) (hne.image complexify) L hL (complexify_normBall M L hML) ε hε hεL
  let q := fun x : RealVector d => p (embedVector x)
  have he0 : ∀ x : RealVector d, embedVector x = 0 ↔ x = 0 := by
    intro x
    rw [← norm_eq_zero, embedVector_norm, norm_eq_zero]
  have hea : ∀ x y : RealVector d, embedVector (x+y) = embedVector x+embedVector y := by
    intro x y
    ext i
    simp [embedVector]
  have hes : ∀ (c : ℝ) (x : RealVector d), embedVector (c • x) = (c : ℂ) • embedVector x := by
    intro c x
    ext i
    simp [embedVector]
  refine ⟨q, ⟨fun x => hp.1 _, fun x => (hp.2.1 _).trans (he0 x), ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    dsimp [q]
    rw [hea]
    exact hp.2.2.1 _ _
  · intro c x
    dsimp [q]
    rw [hes, hp.2.2.2]
    simp
  · intro x
    simpa only [embedVector_norm] using hb (embedVector x)
  · intro A hA x
    have h := hg (complexify A) ⟨A, hA, rfl⟩ (embedVector x)
    simpa only [applyMatrix, complex_action_embed, complexify_radius] using h

#print axioms complex_bounded_comparison_norm
#print axioms real_bounded_comparison_norm
end NLA.MF05.Paper
