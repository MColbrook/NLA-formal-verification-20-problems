module

public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace NLA.RA09.LiteralIntegral

/-- The literal scalar integrand printed in the manuscript. -/
def scalarIntegrand (p x t : ℝ) : ℝ := t ^ (p-1) * x * (x+t)⁻¹

/-- The normalization printed in the manuscript. -/
def normalization (p : ℝ) : ℝ := Real.sin (Real.pi*p) / Real.pi

end NLA.RA09.LiteralIntegral
