module

public import NLA.MF12.Definitions
public import NLA.MF12.PaperDyadicDefinitions
public import Mathlib.Algebra.Order.Floor.Ring

@[expose] public section

set_option autoImplicit false
open Filter
open scoped Topology
noncomputable section
namespace NLA.MF12.Paper

/-- The dimension claimed in the manuscript, including exponent zero. -/
def paperDimension (γ : ℝ) : ℕ :=
  if γ = (⌊γ⌋₊ : ℝ) then ⌊γ⌋₊ + 1 else 6 * (⌊γ⌋₊ + 1)

/-- Two distinct actual matrices, bounds at every positive length, and the
    actual maximal-product nth-root limit. -/
def Realizes {d : ℕ} (A P : Square d) (γ : ℝ) : Prop :=
  A ≠ P ∧ ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    (∀ n : ℕ, 1 ≤ n →
      c * Real.rpow (n : ℝ) γ ≤ familyGrowth (pairFamily A P) n ∧
      familyGrowth (pairFamily A P) n ≤ C * Real.rpow (n : ℝ) γ) ∧
    Tendsto (fun n : ℕ => Real.rpow (familyGrowth (pairFamily A P) n)
      (1 / (n : ℝ))) atTop (𝓝 1)

end NLA.MF12.Paper
