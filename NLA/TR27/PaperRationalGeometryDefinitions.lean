module

public import NLA.TR27.PaperRationalDefinitions
public import NLA.TR27.PaperCoordinates

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

/-- The actual quotient-curve points where the explicit linear denominator
does not vanish. Coordinates are the already certified quotient coordinates. -/
def recoveryOpenPoints (D r : ℕ) (hD : 5 ≤ D) (hr : 3 ≤ r) :
    Set (ℙ ℂ (QuotientSpace D r (chosenParameters r))) :=
  {p | p ∈ quotientPoints D r (chosenParameters r) ∧
    MvPolynomial.eval (quotientCoordinateEquiv D r (by omega) hr p.rep)
      (recoveryDenominator D r hD) ≠ 0}

end NLA.TR27.Paper
