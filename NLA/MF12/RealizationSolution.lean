module

public import NLA.MF12.PaperRealRealization

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

theorem paper_main_realization (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ d : ℕ, d = paperDimension γ ∧ 1 ≤ d ∧
      ∃ A P : Square d, Realizes A P γ ∧
        ((∃ q : ℚ, (q : ℝ) = γ) → ∀ i j, IsDyadic (A i j) ∧ IsDyadic (P i j)) := by
  exact full_main_realization γ hγ

theorem paper_dimension_integer (m : ℕ) : paperDimension (m : ℝ) = m+1 := by
  exact dimension_integer m

theorem paper_dimension_fractional (γ : ℝ) (hγ : 0 < γ) (hγ1 : γ < 1) :
    paperDimension γ = 6 := by
  exact dimension_fractional γ hγ hγ1

theorem paper_dimension_noninteger (γ : ℝ) (hγ : ¬ ∃ m : ℕ, γ = (m : ℝ)) :
    paperDimension γ = 6*(⌊γ⌋₊+1) := by
  exact dimension_noninteger γ hγ

theorem paper_rational_realization (q : ℚ) (hq : 0 ≤ q) :
    ∃ d : ℕ, d = paperDimension (q : ℝ) ∧ 1 ≤ d ∧
      ∃ A P : Square d, Realizes A P (q : ℝ) ∧
        ∀ i j, IsDyadic (A i j) ∧ IsDyadic (P i j) := by
  exact rational_dyadic_realization q hq

theorem paper_two_generators {d : ℕ} (A P : Square d) (γ : ℝ)
    (h : Realizes A P γ) : (pairFamily A P).card = 2 := by
  exact Finset.card_pair h.1

#print axioms paper_main_realization
#print axioms paper_dimension_integer
#print axioms paper_dimension_fractional
#print axioms paper_dimension_noninteger
#print axioms paper_rational_realization
#print axioms paper_two_generators

end NLA.MF12.Paper
