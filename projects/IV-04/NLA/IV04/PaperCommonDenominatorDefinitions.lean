module

public import NLA.IV04.PaperContinuantGrowthDefinitions
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Nat.Size

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational

/-- Sum of the actual canonical rational numerator/denominator binary widths. -/
def rationalPayloadBits {k : ℕ} (q : Fin k → ℚ) : ℕ :=
  ∑ i, ((q i).num.natAbs.size+(q i).den.size)

/-- A computed common denominator, without an assumed divisibility certificate. -/
def rationalCommonDenominator {k : ℕ} (q : Fin k → ℚ) : ℕ :=
  ∏ i, (q i).den

/-- Actual cleared-denominator integer coefficient. -/
def rationalCommonNumerator {k : ℕ} (q : Fin k → ℚ) (i : Fin k) : ℤ :=
  (q i).num*(rationalCommonDenominator q/(q i).den : ℕ)

end IV04.Paper.Computational
