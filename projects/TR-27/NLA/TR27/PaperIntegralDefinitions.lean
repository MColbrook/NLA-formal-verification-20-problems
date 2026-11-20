module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.TR27.Paper

def chosenPowerSumReal (r j : ℕ) : ℝ := ∑ i : Fin r, ((i.val+1 : ℕ) : ℝ)^j
def chosenPowerSum (r j : ℕ) : ℂ := ∑ i : Fin r, ((i.val+1 : ℕ) : ℂ)^j
def chosenPivot (r : ℕ) : ℂ := chosenPowerSum r 1 - 1

end NLA.TR27.Paper
