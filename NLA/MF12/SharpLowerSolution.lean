module

public import NLA.MF12.PaperSharpLower

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.MF12.Paper

theorem paper_parameter_logarithmic_gap (lam : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (n : ℕ) (hn : lam⁻¹ ≤ (n : ℝ)) :
    ∃ q : ℕ, 1 ≤ q ∧ (lam⁻¹)^q ≤ (n : ℝ) ∧ (n : ℝ) < (lam⁻¹)^(q+1) ∧
      1 ≤ n/(q+1) ∧ (1/4:ℝ) ≤ (n/(q+1):ℕ)*parameterLoss lam q := by
  exact parameter_logarithmic_gap lam hlam hlamq n hn

theorem paper_parameter_gain_div_loss (lam α : ℝ) (hlam : 0 < lam) (q : ℕ) (hq : 1 ≤ q) :
    parameterGain (Real.rpow lam (1-α)) q / parameterLoss lam q =
      Real.rpow ((lam⁻¹)^q) α := by
  exact parameter_gain_div_loss lam α hlam q hq

theorem paper_sharp_loss_decay (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (k : ℕ) (hmass : (1/4:ℝ) ≤ (k:ℝ)*ell) :
    1-Real.exp (-1/4) ≤ 1-(1-ell)^k := by
  exact sharp_loss_decay ell hell hell1 k hmass

theorem paper_parameter_repeat_rayleigh (lam μ : ℝ) (q k r : ℕ) (hell : parameterLoss lam q ≠ 0) :
    (parameterGain μ q/parameterLoss lam q)*(1-(1-parameterLoss lam q)^k) ≤
      Real.sqrt 2*spectralNorm (parameterMatrix lam μ^r*(resetMatrix*parameterMatrix lam μ^q)^k) := by
  exact parameter_repeat_rayleigh lam μ q k r hell

theorem paper_parameter_repeat_word (lam μ : ℝ) (q n : ℕ) :
    ∃ w : List Bool, w.length = n ∧
      binaryProduct (parameterMatrix lam μ) resetMatrix w =
        parameterMatrix lam μ^(n-n/(q+1)*(q+1)) *
          (resetMatrix*parameterMatrix lam μ^q)^(n/(q+1)) := by
  exact parameter_repeat_word lam μ q n

theorem paper_parameter_power_norm_ge_one (lam μ : ℝ) (n : ℕ) :
    1 ≤ spectralNorm (parameterMatrix lam μ^n) := by
  exact parameter_power_norm_ge_one lam μ n

theorem paper_parameter_family_sharp_lower (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (n : ℕ) (hn : 1 ≤ n) :
    ((1-Real.exp (-1/4))/Real.sqrt 2*Real.rpow lam α)*Real.rpow (n:ℝ) α ≤
      familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n := by
  exact parameter_family_sharp_lower lam α hlam hlamq hα hα1 n hn

#print axioms paper_parameter_logarithmic_gap
#print axioms paper_parameter_gain_div_loss
#print axioms paper_sharp_loss_decay
#print axioms paper_parameter_repeat_rayleigh
#print axioms paper_parameter_repeat_word
#print axioms paper_parameter_power_norm_ge_one
#print axioms paper_parameter_family_sharp_lower

end NLA.MF12.Paper
