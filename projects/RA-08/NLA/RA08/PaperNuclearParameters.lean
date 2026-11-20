module

public import NLA.RA08.PaperNuclearTailDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

theorem nuclear_choose_eta (ε₀ : ℝ) (hε : 0 < ε₀) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ 1 < (1-η)*(1+ε₀) := by
  let η := ε₀/(2*(1+ε₀))
  have hd : 0 < 2*(1+ε₀) := by positivity
  have hη : 0 < η := div_pos hε hd
  have he : η*(1+ε₀)=ε₀/2 := by
    dsimp [η]
    field_simp
  refine ⟨η,hη,?_,?_⟩
  · dsimp [η]
    apply (div_lt_iff₀ hd).mpr
    nlinarith
  · nlinarith

theorem nuclear_small_time (η D K C ε₀ : ℝ)
    (hη0 : 0 < η) (hη1 : η < 1) (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hε : 0 < ε₀) (hgap : 1 < (1-η)*(1+ε₀)) (hD : C < D) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1/4 ∧ ∀ a : ℝ, 0 < a →
      nuclearLiftTailLower η t ≤ a → a ≤ (1-η)*t →
      0 < t/a-1 ∧ t/a-1 < ε₀ ∧ t=(1+(t/a-1))*a ∧
      (1+C*(t/a-1))*a < t*(η*D+1-η)-K*t^2 := by
  let g := (1-η)-1/(1+ε₀)
  let δ := η*(D-C)
  let L := K+2*C*η*(1-η)
  have hden : 0 < 1+ε₀ := by linarith
  have hg : 0 < g := by
    dsimp [g]
    have hh : 1/(1+ε₀) < 1-η := (div_lt_iff₀ hden).mpr (by nlinarith)
    linarith
  have hδ : 0 < δ := mul_pos hη0 (sub_pos.mpr hD)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hdg : 0 < 2*η*(1-η)+1 := by positivity
  have hdL : 0 < L+1 := by linarith
  have hb : 0 < min (1/4 : ℝ) (min (g/(2*η*(1-η)+1)) (δ/(L+1))) :=
    lt_min (by norm_num) (lt_min (div_pos hg hdg) (div_pos hδ hdL))
  obtain ⟨t,ht,htb⟩ := exists_between hb
  have htq : t < 1/4 := htb.trans_le (min_le_left _ _)
  have htg : t < g/(2*η*(1-η)+1) :=
    htb.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have htL : t < δ/(L+1) :=
    htb.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hgt := (lt_div_iff₀ hdg).mp htg
  have hLt := (lt_div_iff₀ hdL).mp htL
  have hcoeff : 1/(1+ε₀) < (1-η)-2*η*(1-η)*t := by
    dsimp [g] at hgt
    nlinarith
  have hct : t/(1+ε₀) < nuclearLiftTailLower η t := by
    have hh := mul_lt_mul_of_pos_right hcoeff ht
    rw [one_div] at hh
    unfold nuclearLiftTailLower
    rw [div_eq_mul_inv]
    nlinarith
  have hexcess : L*t^2 < δ*t := by
    have hh : L*t < δ := by nlinarith
    have hh' := mul_lt_mul_of_pos_right hh ht
    nlinarith
  refine ⟨t,ht,htq.le,?_⟩
  intro a ha hlow hupp
  have hat : a < t := by nlinarith [mul_pos hη0 ht]
  have hrel : 1 < t/a := (lt_div_iff₀ ha).mpr (by simpa using hat)
  have hrel0 : t/a < 1+ε₀ := by
    apply (div_lt_iff₀ ha).mpr
    have hh : t/(1+ε₀) < a := hct.trans_le hlow
    simpa only [mul_comm] using (div_lt_iff₀ hden).mp hh
  refine ⟨by linarith,by linarith,?_,?_⟩
  · field_simp
    ring
  · have hid : (1+C*(t/a-1))*a=a+C*(t-a) := by
      field_simp
    rw [hid]
    have htail : t-a ≤ η*t+2*η*(1-η)*t^2 := by
      unfold nuclearLiftTailLower at hlow
      nlinarith
    have hc := mul_le_mul_of_nonneg_left htail hC
    dsimp [δ,L] at hexcess
    nlinarith

#print axioms nuclear_small_time
end NLA.RA08.Paper
