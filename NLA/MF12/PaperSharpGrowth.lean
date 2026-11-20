module

public import NLA.MF12.PaperSharpUpper
public import NLA.MF12.PaperSharpLower
public import NLA.MF12.RootLimit

@[expose] public section

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace NLA.MF12.Paper

/-- The same literal general-parameter manuscript pair has nth-root growth
limit one; both quantitative estimates use their printed constants. -/
theorem parameter_sharp_growth (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) :
    (∀ n : ℕ, 1 ≤ n →
      ((1-Real.exp (-1/4))/Real.sqrt 2*Real.rpow lam α)*Real.rpow (n:ℝ) α ≤
        familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n ∧
      familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n ≤
        (2*Real.sqrt 6/(1-Real.rpow lam (1-α))^2)*Real.rpow (n:ℝ) α) ∧
    Tendsto (fun n : ℕ => Real.rpow
      (familyGrowth (pairFamily (parameterMatrix lam (Real.rpow lam (1-α))) resetMatrix) n)
      (1/(n:ℝ))) atTop (𝓝 1) := by
  have hbounds (n : ℕ) (hn : 1 ≤ n) :=
    And.intro (parameter_family_sharp_lower lam α hlam hlamq hα hα1 n hn)
      (parameter_family_sharp_upper lam α hlam hlamq hα hα1 n hn)
  refine ⟨hbounds, ?_⟩
  have hδ : 0 < 1-Real.exp (-1/4) := by
    have h := Real.exp_lt_one_iff.mpr (by norm_num : (-1/4:ℝ) < 0)
    linarith
  have hμ1 : Real.rpow lam (1-α) < 1 :=
    Real.rpow_lt_one hlam.le (by linarith) (by linarith)
  apply roots_of_polynomial_growth _ α
    ((1-Real.exp (-1/4))/Real.sqrt 2*Real.rpow lam α)
    (2*Real.sqrt 6/(1-Real.rpow lam (1-α))^2) hα.le _ _ hbounds
  · exact mul_pos (div_pos hδ (Real.sqrt_pos.mpr (by norm_num))) (Real.rpow_pos_of_pos hlam α)
  · exact div_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr (by norm_num)))
      (sq_pos_of_pos (sub_pos.mpr hμ1))

#print axioms parameter_sharp_growth
end NLA.MF12.Paper
