module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CycleProfile
open scoped BigOperators

def Delta (t : ℝ) (j : ℕ) : ℝ := Real.arcsin (t / (2 : ℝ)^j)
def Height (R : ℕ) (t : ℝ) (j : ℕ) : ℝ := ∑ s ∈ Finset.Ico j R, Delta t s
def Balance (R : ℕ) (t : ℝ) : ℝ := 3 * Real.arcsin t + 2 * ∑ j ∈ Finset.Ico 1 R, Delta t j
end Reference.MD06CycleProfile
