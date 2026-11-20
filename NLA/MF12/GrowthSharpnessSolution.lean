module

public import NLA.MF12.PaperGrowthSharpness

@[expose] public section

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology
namespace NLA.MF12.Paper

theorem paper_jordan_entry (m n : ℕ) :
    (jordanMatrix m ^ n) (0 : Fin (m+1)) ⟨m, by omega⟩ = (n.choose m : ℝ) := by
  exact jordan_top_right m n

theorem paper_jordan_asymptotic (m : ℕ) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (jordanMatrix m ^ n) (0 : Fin (m+1)) ⟨m, by omega⟩)
      (fun n : ℕ => (n : ℝ)^m / (m.factorial : ℝ)) := by
  exact jordan_top_right_asymptotic m

theorem paper_jordan_radius (m : ℕ) :
    Tendsto (fun n : ℕ => Real.rpow (spectralNorm (jordanMatrix m ^ n)) (1/(n : ℝ)))
      atTop (𝓝 1) := by
  exact jordan_root_limit m

theorem paper_growth_exponent_sharp (m : ℕ) (β C : ℝ) (hβ : β < (m : ℝ)) (N : ℕ) :
    ∃ n : ℕ, max 1 N ≤ n ∧ C * Real.rpow (n : ℝ) β < spectralNorm (jordanMatrix m ^ n) := by
  exact jordan_no_smaller_exponent m β C hβ N

#print axioms paper_jordan_entry
#print axioms paper_jordan_asymptotic
#print axioms paper_jordan_radius
#print axioms paper_growth_exponent_sharp

end NLA.MF12.Paper
