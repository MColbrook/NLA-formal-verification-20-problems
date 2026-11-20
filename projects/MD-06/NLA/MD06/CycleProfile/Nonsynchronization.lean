module

public import NLA.MD06.CycleProfile.Profile
public import NLA.MD06.LaplacianSpectralGap.Gap

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleProfile
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction Reference.MD06Spectral

theorem actual_small_correction_preserves_nonsynchronization {n : ℕ}
    (phi h : Configuration n) (i j : Fin n) (hij : i ≠ j)
    (hforce : (1/2 : ℝ) < |Real.sin (phi i-phi j)|)
    (hsmall : ‖h‖ < 1/(2*Real.sqrt 2)) :
    ¬Synchronized (PhaseLift (fun a => phi a+h a)) := by
  intro hsync
  have he : Real.sin ((phi i+h i)-(phi j+h j)) = 0 := by
    have heq : PhaseLift (fun a => phi a+h a) i - PhaseLift (fun a => phi a+h a) j = 0 :=
      sub_eq_zero.mpr (hsync i j)
    have hs := congrArg Real.Angle.sin heq
    rw [Real.Angle.sin_zero] at hs
    change Real.Angle.sin (((phi i+h i : ℝ) : Real.Angle)-((phi j+h j : ℝ) : Real.Angle)) = 0 at hs
    rw [←Real.Angle.coe_sub,Real.Angle.sin_coe] at hs
    exact hs
  have hl := Real.abs_sin_sub_sin_le (phi i-phi j) ((phi i+h i)-(phi j+h j))
  have ht : (phi i-phi j)-((phi i+h i)-(phi j+h j)) = -(h i-h j) := by ring
  rw [he,sub_zero,ht,abs_neg] at hl
  have hb := actual_euclidean_edge_difference_bound h i j hij
  have hp : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hm : Real.sqrt 2*‖h‖ < (1/2 : ℝ) := by
    rw [mul_comm]
    apply (lt_div_iff₀ hp).mp
    simpa only [div_div] using hsmall
  linarith

theorem actual_sorted_gap_nonsynchronized_correction {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 2 ≤ n) (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : gamma ≤ LaplacianGap G hn)
    (phi : Configuration n) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hcos : ∀ i j, G.Adj i j → c ≤ Real.cos (phi i-phi j))
    (hsmall : ‖GradientVector G phi‖ < c^2*gamma/(4*Real.sqrt 2))
    (i j : Fin n) (hij : i ≠ j) (hforce : (1/2 : ℝ) < |Real.sin (phi i-phi j)|) :
    ∃ h : Configuration n, (∑ i, h i) = 0 ∧ ‖h‖ < c/(2*Real.sqrt 2) ∧
      (∀ i, Gradient G (PhaseLift (fun a => phi a+h a)) i = 0) ∧
      IsLocalMin (Energy G) (PhaseLift (fun a => phi a+h a)) ∧
      (∀ i j, G.Adj i j → c/2 ≤ Real.cos ((phi i+h i)-(phi j+h j))) ∧
      (∀ z : Configuration n, (∑ i, z i) = 0 →
        (c*gamma/2)*‖z‖^2 ≤ HessianQuadratic G (PhaseLift (fun a => phi a+h a)) (fun i => z i)) ∧
      ¬Synchronized (PhaseLift (fun a => phi a+h a)) := by
  obtain ⟨h,hm,hb,hg0,hl,hcos0,hh⟩ := actual_sorted_gap_quantitative_correction
    G hg hn gamma hgamma hgap phi c hc hcos hsmall
  refine ⟨h,hm,hb,hg0,hl,hcos0,hh,?_⟩
  apply actual_small_correction_preserves_nonsynchronization phi h i j hij hforce
  exact hb.trans_le (div_le_div_of_nonneg_right hc1 (by positivity))

theorem actual_profile_opposite_root_sine_gt_half {R : ℕ} (hR : 4 ≤ R) :
    (1/2 : ℝ) < |Real.sin (2 * Height R (Root R) 0)| := by
  rw [actual_opposite_root_sine hR,abs_neg,abs_of_nonneg (actual_root_spec hR).1.1]
  exact (actual_root_interval hR).1
end Reference.MD06CycleProfile
