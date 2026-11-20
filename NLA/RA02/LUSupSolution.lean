module

public import NLA.RA02.PaperLUSup
public import NLA.RA02.PaperCholeskySup

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem paper_sup_lu_expectedError_best_upper_positive {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ)
    (ht : 0 < rectangularBestRankErrorSquared A r) :
    NLA.RA03.expectedError A r ≤ (4:ℝ)^r*rectangularBestRankErrorSquared A r := by
  exact lu_expectedError_best_upper_positive A r ht

theorem paper_sup_rectangular_best_error_attained {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) :
    ∃ B : Matrix (Fin m) (Fin n) ℂ, B.rank ≤ r ∧
      NLA.RA03.frobeniusSq (A-B) = gramTail A r := by
  exact rectangular_best_error_attained A r

theorem paper_sup_rectangularBest_eq_gramTail {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) :
    rectangularBestRankErrorSquared A r = gramTail A r := by
  exact rectangularBest_eq_gramTail A r

theorem paper_sup_gramTail_le_lowRankError {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ)
    (r : ℕ) (hB : B.rank ≤ r) : gramTail A r ≤ NLA.RA03.frobeniusSq (A-B) := by
  exact gramTail_le_lowRankError A B r hB

theorem paper_sup_rectangularBest_eq_squareBest {n : ℕ} (A : NLA.RA02.Square n) (r : ℕ) :
    rectangularBestRankErrorSquared A r = bestRankErrorSquared A r := by
  exact rectangularBest_eq_squareBest A r

theorem paper_sup_luRatios_isLUB (r : ℕ) : IsLUB (luRatios r) ((4:ℝ)^r) := by
  exact luRatios_isLUB r

theorem paper_sup_realPositiveLURatios_isLUB (r : ℕ) : IsLUB (realPositiveLURatios r) ((4:ℝ)^r) := by
  exact realPositiveLURatios_isLUB r

theorem paper_sup_best_error_semantics {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) :
    rectangularBestRankErrorSquared A r = sInf {e : ℝ | ∃ B : Matrix (Fin m) (Fin n) ℂ, B.rank ≤ r ∧ NLA.RA03.frobeniusSq (A-B) = e} := by
  exact rfl

theorem paper_sup_lu_ratios_semantics (r : ℕ) (x : ℝ) :
    x ∈ luRatios r ↔ ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ), 0 < rectangularBestRankErrorSquared A r ∧ x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r := by
  exact Iff.rfl

theorem paper_sup_real_positive_lu_ratios_semantics (r : ℕ) (x : ℝ) :
    x ∈ realPositiveLURatios r ↔ ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef), (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧ 0 < rectangularBestRankErrorSquared A r ∧ x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r := by
  exact Iff.rfl

theorem paper_sup_worst_case_constants (r : ℕ) :
    IsLUB (choleskyRatios r) ((2:ℝ)^r) ∧ IsLUB (realPositiveCholeskyRatios r) ((2:ℝ)^r) ∧ IsLUB (luRatios r) ((4:ℝ)^r) ∧ IsLUB (realPositiveLURatios r) ((4:ℝ)^r) := by
  exact ⟨choleskyRatios_isLUB r, realPositiveCholeskyRatios_isLUB r, luRatios_isLUB r, realPositiveLURatios_isLUB r⟩

#print axioms NLA.RA02.Paper.paper_sup_lu_expectedError_best_upper_positive
#print axioms NLA.RA02.Paper.paper_sup_rectangular_best_error_attained
#print axioms NLA.RA02.Paper.paper_sup_rectangularBest_eq_gramTail
#print axioms NLA.RA02.Paper.paper_sup_gramTail_le_lowRankError
#print axioms NLA.RA02.Paper.paper_sup_rectangularBest_eq_squareBest
#print axioms NLA.RA02.Paper.paper_sup_luRatios_isLUB
#print axioms NLA.RA02.Paper.paper_sup_realPositiveLURatios_isLUB
#print axioms NLA.RA02.Paper.paper_sup_best_error_semantics
#print axioms NLA.RA02.Paper.paper_sup_lu_ratios_semantics
#print axioms NLA.RA02.Paper.paper_sup_real_positive_lu_ratios_semantics
#print axioms NLA.RA02.Paper.paper_sup_worst_case_constants
end NLA.RA02.Paper
