module

public import NLA.IE21.ThresholdSelectors.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NLA.IE21.GeneralCoupling

/-- The actual extended expectation of the absolute difference on the coupling
space, so infinite expectation is represented by infinity rather than a default
real Bochner integral. -/
def couplingDistance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y Z : Ω → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal |Y ω - Z ω| ∂μ

end NLA.IE21.GeneralCoupling
