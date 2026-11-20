module

public import NLA.TR27.PaperHomogeneousDefinitions
public import NLA.TR27.PaperSourceBorderDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.TR27.Paper

def projectedSecant (D r : ℕ) (t : ℂ) : QuotientSpace D r (chosenParameters r) :=
  quotientProjection D r (chosenParameters r) (secantSlope D t)

def projectedBorderPolynomial (D r : ℕ) (hD : 2 ≤ D) (j : Fin D) : Polynomial ℂ :=
  Polynomial.C (chosenPivot r) *
    (if (retainedIndex D hD j).val = 0 then 0 else
      Polynomial.X ^ ((retainedIndex D hD j).val-1)) -
    Polynomial.C (chosenPowerSum r (retainedIndex D hD j).val)

def projectedBorderSubstitution (D r : ℕ) (hD : 2 ≤ D) :
    ImageCoordinatePolynomial D →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (projectedBorderPolynomial D r hD)

end NLA.TR27.Paper
