module

public import NLA.MD06.MainAssembly.RadiusDefinitions
public import NLA.MD06.CycleProfile.NumericMargin
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MainAssembly
open Reference.MD06CycleProfile

theorem actual_paper_radius_at_least_four (ell : ℕ) : 4≤PaperRadius ell := by
  unfold PaperRadius
  omega

theorem actual_paper_radius_inequality (ell : ℕ) (hell : 0<ell) :
    32*(ell : ℝ)/((Real.sqrt (1-(Root 4)^2))^4*(1/10 : ℝ)^2)<
      (2 : ℝ)^(PaperRadius ell-1) := by
  let c : ℝ:=Real.sqrt (1-(Root 4)^2)
  have hc : (1/16 : ℝ)<c := actual_uniform_cosine_gt_sixteenth
  have hc0 : 0<c := by linarith
  have hs : (1/256 : ℝ)<c^2 := by nlinarith
  have hs0 : 0<c^2+1/256 := by positivity
  have hm:=mul_pos (sub_pos.mpr hs) hs0
  have h4 : (1/65536 : ℝ)<c^4 := by nlinarith
  have hd : 0<c^4*(1/10 : ℝ)^2 := by positivity
  have hp : (0 : ℝ)<ell := by exact_mod_cast hell
  have hb : 32*(ell : ℝ)/(c^4*(1/10 : ℝ)^2)<209715200*(ell : ℝ) := by
    apply (div_lt_iff₀ hd).mpr
    have hmul:=mul_pos (sub_pos.mpr h4) hp
    nlinarith
  have hpow : (ell : ℝ)≤(2 : ℝ)^Nat.clog 2 ell := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1<2) ell
  have hr : PaperRadius ell-1=28+Nat.clog 2 ell := by unfold PaperRadius;omega
  change 32*(ell : ℝ)/(c^4*(1/10 : ℝ)^2)<_
  calc
    _ < 209715200*(ell : ℝ) := hb
    _ < 268435456*(ell : ℝ) := by nlinarith
    _ ≤ 268435456*(2 : ℝ)^Nat.clog 2 ell := mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = (2 : ℝ)^(PaperRadius ell-1) := by rw [hr,pow_add];norm_num

#print axioms actual_paper_radius_at_least_four
#print axioms actual_paper_radius_inequality
end Reference.MD06MainAssembly
