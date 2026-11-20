module

public import NLA.TR27.PaperProjectionDefinitions
public import NLA.TR27.PaperSourceBorderDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.TR27.Paper

/-- The divided secant in the quotient for the supplied parameters. -/
def parameterSecant (D r : ℕ) (a : Fin r → Option ℂ) (t : ℂ) :
    QuotientSpace D r a :=
  quotientProjection D r a (secantSlope D t)

end NLA.TR27.Paper
