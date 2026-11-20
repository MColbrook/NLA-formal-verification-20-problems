module

public import NLA.RA02.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
namespace NLA.RA02.Paper

/-- Ratios for arbitrary complex PSD inputs with a positive rank-r tail. -/
def choleskyRatios (r : ℕ) : Set ℝ :=
  {x | ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosSemidef), r ≤ n ∧
    0 < NLA.RA02.rankTail A hA.isHermitian r ∧
    x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r}

/-- Restriction to real, positive-definite, entrywise-positive inputs. -/
def realPositiveCholeskyRatios (r : ℕ) : Set ℝ :=
  {x | ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef),
    (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧ r ≤ n ∧
    0 < NLA.RA02.rankTail A hA.isHermitian r ∧
    x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r}

end NLA.RA02.Paper
