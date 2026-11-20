module

public import NLA.MF12.PaperIrrational

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

theorem paper_irrational_exponent  :
    0 < 1-Real.log 3/Real.log 4 ∧ 1-Real.log 3/Real.log 4 < 1 ∧
      Irrational (1-Real.log 3/Real.log 4) := by
  exact irrational_exponent_bounds

theorem paper_irrational_rational_pair  :
    Realizes (fractionalMatrix (1-Real.log 3/Real.log 4)) resetMatrix
      (1-Real.log 3/Real.log 4) ∧
    ∀ i j : Fin 6,
      (∃ q : ℚ, (q : ℝ) = fractionalMatrix (1-Real.log 3/Real.log 4) i j) ∧
      (∃ q : ℚ, (q : ℝ) = resetMatrix i j) := by
  exact ⟨irrational_pair_realization, irrational_pair_entries⟩

theorem paper_rational_density (x ε : ℝ) (hx : 0 ≤ x) (hε : 0 < ε) :
    ∃ γ : ℝ, 0 ≤ γ ∧ |γ-x| < ε ∧
      ∃ d : ℕ, 1 ≤ d ∧ ∃ A P : Square d, Realizes A P γ ∧
        ∀ i j, (∃ q : ℚ, (q : ℝ) = A i j) ∧ (∃ q : ℚ, (q : ℝ) = P i j) := by
  exact rational_exponents_dense x ε hx hε

#print axioms paper_irrational_exponent
#print axioms paper_irrational_rational_pair
#print axioms paper_rational_density

end NLA.MF12.Paper
