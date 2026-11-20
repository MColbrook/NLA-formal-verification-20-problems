module

public import NLA.MF12.PaperSharpGrowth

@[expose] public section

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace NLA.MF12.Paper

theorem paper_parameter_sharp_growth (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) :
    (∀ n : ℕ, 1 ≤ n →
      ((1-Real.exp (-1/4))/Real.sqrt 2*Real.rpow lam α)*Real.rpow (n:ℝ) α ≤
        familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n ∧
      familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n ≤
        (2*Real.sqrt 6/(1-Real.rpow lam (1-α))^2)*Real.rpow (n:ℝ) α) ∧
    Tendsto (fun n : ℕ => Real.rpow
      (familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n)
      (1/(n:ℝ))) atTop (𝓝 1) := by
  exact parameter_sharp_growth lam α hlam hlamq hα hα1

#print axioms paper_parameter_sharp_growth

end NLA.MF12.Paper
