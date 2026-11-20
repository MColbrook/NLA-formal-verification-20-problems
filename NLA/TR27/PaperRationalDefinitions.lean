module

public import NLA.TR27.PaperHomogeneousDefinitions
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.TR27.Paper

def recoveryMomentA (r : ℕ) : ℂ :=
  chosenPowerSum r 3 * chosenPowerSum r 5 - chosenPowerSum r 4 ^ 2

def recoveryMomentB (r : ℕ) : ℂ :=
  chosenPowerSum r 3 * chosenPowerSum r 4 - chosenPowerSum r 2 * chosenPowerSum r 5

def recoveryMomentC (r : ℕ) : ℂ :=
  chosenPowerSum r 2 * chosenPowerSum r 4 - chosenPowerSum r 3 ^ 2

/-- Coordinates numbered 2,3,4,5 in the source, retained after deleting number 1. -/
def recoveryIndex (D : ℕ) (hD : 5 ≤ D) (j : Fin 4) : Fin D := ⟨j.val+1, by omega⟩

def recoveryDenominator (D r : ℕ) (hD : 5 ≤ D) : ImageCoordinatePolynomial D :=
  MvPolynomial.C (recoveryMomentA r) * MvPolynomial.X (recoveryIndex D hD 0) +
  MvPolynomial.C (recoveryMomentB r) * MvPolynomial.X (recoveryIndex D hD 1) +
  MvPolynomial.C (recoveryMomentC r) * MvPolynomial.X (recoveryIndex D hD 2)

def recoveryNumerator (D r : ℕ) (hD : 5 ≤ D) : ImageCoordinatePolynomial D :=
  MvPolynomial.C (recoveryMomentA r) * MvPolynomial.X (recoveryIndex D hD 1) +
  MvPolynomial.C (recoveryMomentB r) * MvPolynomial.X (recoveryIndex D hD 2) +
  MvPolynomial.C (recoveryMomentC r) * MvPolynomial.X (recoveryIndex D hD 3)

def recoveryPolynomial (r : ℕ) : Polynomial ℂ :=
  Polynomial.C (chosenPivot r) * Polynomial.X^2 *
    (Polynomial.C (recoveryMomentA r) + Polynomial.C (recoveryMomentB r)*Polynomial.X +
      Polynomial.C (recoveryMomentC r)*Polynomial.X^2)

def rationalRecovery (D r : ℕ) (hD : 5 ≤ D) (w : Fin D → ℂ) : ℂ :=
  MvPolynomial.eval w (recoveryNumerator D r hD) /
    MvPolynomial.eval w (recoveryDenominator D r hD)

end NLA.TR27.Paper
