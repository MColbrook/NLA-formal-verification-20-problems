module

public import NLA.IE21.ThresholdSelectors.Definitions
public import Mathlib.Probability.CDF

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal
namespace NLA.IE21.QuantileIntegral
open ThresholdSelectors

/-- The lower quantile, defined as the generalized inverse of the actual CDF.
Only its values on the open probability interval are used. -/
def lowerQuantile (μ : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf μ x}


/-- Selectors explicitly restricted to measurable functions of the variable. -/
def variableOnlyTrim {Ω : Type*} [MeasurableSpace Ω]
    (θ : ℝ) (μ : Measure Ω) (Y : Ω → ℝ) : ℝ≥0∞ :=
  sInf {z | ∃ v : ℝ → ℝ, Measurable v ∧ (∀ y, 0 ≤ v y ∧ v y ≤ 1) ∧
    Feasible μ θ (v ∘ Y) ∧ z = selectorCost μ Y (v ∘ Y)}

end NLA.IE21.QuantileIntegral
