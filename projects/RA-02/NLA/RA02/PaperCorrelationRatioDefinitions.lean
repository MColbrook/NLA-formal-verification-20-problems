module

public import NLA.RA02.PaperCholeskySupDefinitions
public import NLA.RA02.PaperLUSupDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
namespace NLA.RA02.Paper

/-- Actual Cholesky ratios for the real, positive-definite, entrywise-positive,
unit-diagonal inputs specified in the correlation proposition. -/
def correlationCholeskyRatios (r : ℕ) : Set ℝ :=
  {x | ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef),
    (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧
    (∀ i, A i i = 1) ∧ r ≤ n ∧
    0 < NLA.RA02.rankTail A hA.isHermitian r ∧
    x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r}

/-- Actual LU ratios for the same correlation inputs, using the best rank-at-most-r
squared Frobenius-error infimum as the denominator. -/
def correlationLURatios (r : ℕ) : Set ℝ :=
  {x | ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef),
    (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧
    (∀ i, A i i = 1) ∧
    0 < rectangularBestRankErrorSquared A r ∧
    x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r}

end NLA.RA02.Paper
