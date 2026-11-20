module

public import NLA.MF12.LiteralDyadic.Growth

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace NLA.MF12.LiteralDyadic.Interface
open NLA.MF12 NLA.MF12.Paper

theorem actual_rational_parameters (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    2 ≤ b ∧ 0 < (a:ℝ)/(b:ℝ) ∧ (a:ℝ)/(b:ℝ) < 1 ∧
      0 < Real.rpow 2 (-(b:ℝ)) ∧ Real.rpow 2 (-(b:ℝ)) ≤ 1/4 ∧
      Real.rpow 2 (-((b-a:ℕ):ℝ)) =
        Real.rpow (Real.rpow 2 (-(b:ℝ))) (1-(a:ℝ)/(b:ℝ)) ∧
      IsDyadic (Real.rpow 2 (-(b:ℝ))) ∧ IsDyadic (Real.rpow 2 (-((b-a:ℕ):ℝ))) := by
  exact RootMF12LiteralDyadic.actual_rational_parameters a b ha hab

theorem actual_literal_entries (a b m : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (∀ i j, IsDyadic (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ))) i j) ∧ IsDyadic (resetMatrix i j)) ∧
    (∀ i j, IsDyadic (tensor (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ)))) (jordanMatrix m) i j) ∧
      IsDyadic (tensor resetMatrix (jordanMatrix m) i j)) := by
  exact RootMF12LiteralDyadic.actual_literal_entries a b m ha hab

theorem actual_literal_growth (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (∀ n : ℕ, 1 ≤ n →
      ((1-Real.exp (-1/4))/Real.sqrt 2*Real.rpow (Real.rpow 2 (-(b:ℝ))) ((a:ℝ)/(b:ℝ)))*Real.rpow (n:ℝ) ((a:ℝ)/(b:ℝ)) ≤
        familyGrowth (pairFamily (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ)))) resetMatrix) n ∧
      familyGrowth (pairFamily (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ)))) resetMatrix) n ≤
        (2*Real.sqrt 6/(1-Real.rpow 2 (-((b-a:ℕ):ℝ)))^2)*Real.rpow (n:ℝ) ((a:ℝ)/(b:ℝ))) ∧
    Tendsto (fun n : ℕ => Real.rpow
      (familyGrowth (pairFamily (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ)))) resetMatrix) n)
      (1/(n:ℝ))) atTop (𝓝 1) := by
  exact RootMF12LiteralDyadic.actual_literal_growth a b ha hab

end NLA.MF12.LiteralDyadic.Interface
