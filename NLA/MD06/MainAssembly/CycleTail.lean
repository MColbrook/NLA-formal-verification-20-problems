module

public import NLA.MD06.MainAssembly.RadiusChoice
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MainAssembly
open Filter Topology

theorem actual_fourfold_cycle_mean_lower (q : ℕ) :
    (q : ℝ)+1≤(2 : ℝ)^(4*(q+1))/(2*(4*(q+1) : ℕ)) := by
  have h (j : ℕ) : 8*((j : ℝ)+1)^2≤(16 : ℝ)^(j+1) := by
    induction j with
    | zero => norm_num
    | succ j ih =>
      have hj : (0 : ℝ)≤j := Nat.cast_nonneg j
      push_cast
      conv_rhs => rw [pow_succ]
      have hm:=mul_le_mul_of_nonneg_right ih (by norm_num : (0 : ℝ)≤16)
      nlinarith
  have hp : (2 : ℝ)^(4*(q+1))=(16 : ℝ)^(q+1) := by rw [pow_mul];norm_num
  rw [hp]
  have hd : (0 : ℝ)<2*(4*(q+1) : ℕ) := by positivity
  apply (le_div_iff₀ hd).mpr
  have hh:=h q
  push_cast
  nlinarith

theorem actual_fourfold_no_cycle_target_tendsto_zero :
    Tendsto (fun q : ℕ=>Real.exp (-((2 : ℝ)^(4*(q+1))/(2*(4*(q+1) : ℕ)))))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun q : ℕ=>(q : ℝ)+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    obtain ⟨N,hN⟩:=exists_nat_gt b
    filter_upwards [eventually_ge_atTop N] with q hq
    have hq' : (N : ℝ)≤q := by exact_mod_cast hq
    linarith
  have he:=Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ht)
  change Tendsto (fun q : ℕ=>Real.exp (-((q : ℝ)+1))) atTop (𝓝 0) at he
  apply squeeze_zero (fun _=> (Real.exp_pos _).le) ?_ he
  intro q
  apply Real.exp_le_exp.mpr
  linarith [actual_fourfold_cycle_mean_lower q]

#print axioms actual_fourfold_cycle_mean_lower
#print axioms actual_fourfold_no_cycle_target_tendsto_zero
end Reference.MD06MainAssembly
