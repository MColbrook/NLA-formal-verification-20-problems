module

public import NLA.MF12.LiteralDyadic.Proof
public import NLA.MF12.PaperSharpGrowth

@[expose] public section
set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace RootMF12LiteralDyadic
open NLA.MF12 NLA.MF12.Paper

theorem actual_literal_growth (a b : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (∀ n : ℕ, 1 ≤ n →
      ((1-Real.exp (-1/4))/Real.sqrt 2*Real.rpow (Real.rpow 2 (-(b:ℝ))) ((a:ℝ)/(b:ℝ)))*Real.rpow (n:ℝ) ((a:ℝ)/(b:ℝ)) ≤
        familyGrowth (pairFamily (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ)))) resetMatrix) n ∧
      familyGrowth (pairFamily (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ)))) resetMatrix) n ≤
        (2*Real.sqrt 6/(1-Real.rpow 2 (-((b-a:ℕ):ℝ)))^2)*Real.rpow (n:ℝ) ((a:ℝ)/(b:ℝ))) ∧
    Tendsto (fun n : ℕ => Real.rpow
      (familyGrowth (pairFamily (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ)))) resetMatrix) n)
      (1/(n:ℝ))) atTop (𝓝 1) := by
  obtain ⟨hb,hapos,haone,hlam,hlamq,hmu,_,_⟩ := actual_rational_parameters a b ha hab
  simpa only [← hmu] using parameter_sharp_growth (Real.rpow 2 (-(b:ℝ))) ((a:ℝ)/(b:ℝ)) hlam hlamq hapos haone

theorem actual_literal_entries (a b m : ℕ) (ha : 1 ≤ a) (hab : a < b) :
    (∀ i j, IsDyadic (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ))) i j) ∧ IsDyadic (resetMatrix i j)) ∧
    (∀ i j, IsDyadic (tensor (parameterMatrix (Real.rpow 2 (-(b:ℝ))) (Real.rpow 2 (-((b-a:ℕ):ℝ)))) (jordanMatrix m) i j) ∧
      IsDyadic (tensor resetMatrix (jordanMatrix m) i j)) := by
  obtain ⟨_,_,_,_,_,_,hlam,hmu⟩ := actual_rational_parameters a b ha hab
  have h := actual_parameter_entries_dyadic _ _ hlam hmu
  exact ⟨h,fun i j => ⟨actual_tensor_dyadic _ _ (fun i j => (h i j).1) (actual_jordan_entries_dyadic m) i j,
    actual_tensor_dyadic _ _ (fun i j => (h i j).2) (actual_jordan_entries_dyadic m) i j⟩⟩

#print axioms actual_literal_growth
#print axioms actual_literal_entries
end RootMF12LiteralDyadic
