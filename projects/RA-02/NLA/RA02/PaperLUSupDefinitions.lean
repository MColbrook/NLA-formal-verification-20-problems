module

public import NLA.RA02.PaperRectangularBestDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
namespace NLA.RA02.Paper

/-- Actual LU ratios over all complex rectangular matrix inputs with positive
best rank-r squared Frobenius error. No dimension or nonsingularity condition. -/
def luRatios (r : ℕ) : Set ℝ :=
  {x | ∃ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℂ),
    0 < rectangularBestRankErrorSquared A r ∧
    x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r}

/-- The same ratios restricted to real positive-definite, entrywise-positive inputs. -/
def realPositiveLURatios (r : ℕ) : Set ℝ :=
  {x | ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef),
    (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧
    0 < rectangularBestRankErrorSquared A r ∧
    x = NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r}

end NLA.RA02.Paper
