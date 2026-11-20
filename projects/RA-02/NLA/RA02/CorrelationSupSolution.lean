module

public import NLA.RA02.PaperCorrelationSup

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
namespace NLA.RA02.Paper

theorem paper_correlation_exists_correlation_cholesky_above (r : ℕ) (q : ℝ) (hq : q < (2 : ℝ)^r) :
    ∃ x ∈ correlationCholeskyRatios r, q < x := by
  exact exists_correlation_cholesky_above r q hq

theorem paper_correlation_exists_correlation_lu_above (r : ℕ) (q : ℝ) (hq : q < (4 : ℝ)^r) :
    ∃ x ∈ correlationLURatios r, q < x := by
  exact exists_correlation_lu_above r q hq

theorem paper_correlation_correlationCholeskyRatios_isLUB (r : ℕ) :
    IsLUB (correlationCholeskyRatios r) ((2 : ℝ)^r) := by
  exact correlationCholeskyRatios_isLUB r

theorem paper_correlation_correlationLURatios_isLUB (r : ℕ) :
    IsLUB (correlationLURatios r) ((4 : ℝ)^r) := by
  exact correlationLURatios_isLUB r

theorem paper_correlation_sharp_correlation_suprema (r : ℕ) :
    IsLUB (correlationCholeskyRatios r) ((2 : ℝ)^r) ∧
      IsLUB (correlationLURatios r) ((4 : ℝ)^r) := by
  exact sharp_correlation_suprema r

theorem paper_correlation_cholesky_class_semantics (r : ℕ) (x : ℝ) :
    x ∈ correlationCholeskyRatios r ↔
      ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef),
        (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧
        (∀ i, A i i = 1) ∧ 0 < NLA.RA02.rankTail A hA.isHermitian r ∧
        x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r := by
  constructor
  · rintro ⟨n,A,hA,hp,hd,_,ht,hx⟩
    exact ⟨n,A,hA,hp,hd,ht,hx⟩
  · rintro ⟨n,A,hA,hp,hd,ht,hx⟩
    exact ⟨n,A,hA,hp,hd,positive_rankTail_dimension A hA.isHermitian r ht,ht,hx⟩

theorem paper_correlation_lu_class_semantics (r : ℕ) (x : ℝ) :
    x ∈ correlationLURatios r ↔
      ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef),
        (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧
        (∀ i, A i i = 1) ∧ 0 < rectangularBestRankErrorSquared A r ∧
        x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r := by
  rfl

theorem paper_sharpness_for_correlation_matrices (r : ℕ) (_hr : 1 ≤ r) :
    IsLUB (correlationCholeskyRatios r) ((2 : ℝ)^r) ∧
      IsLUB (correlationLURatios r) ((4 : ℝ)^r) := by
  exact sharp_correlation_suprema r

#print axioms NLA.RA02.Paper.paper_correlation_exists_correlation_cholesky_above
#print axioms NLA.RA02.Paper.paper_correlation_exists_correlation_lu_above
#print axioms NLA.RA02.Paper.paper_correlation_correlationCholeskyRatios_isLUB
#print axioms NLA.RA02.Paper.paper_correlation_correlationLURatios_isLUB
#print axioms NLA.RA02.Paper.paper_correlation_sharp_correlation_suprema
#print axioms NLA.RA02.Paper.paper_correlation_cholesky_class_semantics
#print axioms NLA.RA02.Paper.paper_correlation_lu_class_semantics
#print axioms NLA.RA02.Paper.paper_sharpness_for_correlation_matrices
end NLA.RA02.Paper
