module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Real.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06DivisorTrace
open scoped BigOperators

def DivisorTraceContribution (n t : ℕ) : ℝ :=
  ∑ l ∈ t.divisors, 3 * (n : ℝ) * (2 : ℝ) ^ l / (3 * (n : ℝ) - 2 * (l : ℝ) + 1)

end Reference.RootMD06DivisorTrace
