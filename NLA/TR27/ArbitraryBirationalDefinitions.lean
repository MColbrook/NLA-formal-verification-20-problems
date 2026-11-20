module

public import NLA.TR27.ArbitraryRecoveryDefinitions
public import NLA.TR27.ArbitraryCoordinates

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped Classical LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

def parameterBirationalNumerator (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) : ImageCoordinatePolynomial D :=
  parameterRecoveryNumerator D r hD hr a * MvPolynomial.X ⟨0,by omega⟩

def parameterBirationalDenominator (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) : ImageCoordinatePolynomial D :=
  parameterRecoveryDenominator D r hD a * MvPolynomial.X ⟨0,by omega⟩

def parameterBirationalException (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) : Polynomial ℂ :=
  parameterRecoveryException D r hD a * parameterAffinePolynomial D r a ⟨0,by omega⟩

def parameterBirationalOpen (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) :
    Set (ℙ ℂ (QuotientSpace D r (fun i => some (a i)))) :=
  {p | p ∈ quotientPoints D r (fun i => some (a i)) ∧
    MvPolynomial.eval (parameterCoordinateEquiv D r hr a p.rep)
      (parameterBirationalDenominator D r hr hD a) ≠ 0}

def parameterBirationalRecovery (D r : ℕ) (hr : 1 ≤ r)
    (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) (w : Fin D → ℂ) : ℂ :=
  MvPolynomial.eval w (parameterBirationalNumerator D r hr hD a) /
    MvPolynomial.eval w (parameterBirationalDenominator D r hr hD a)

end NLA.TR27.Paper
