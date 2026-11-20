module

public import NLA.TR27.ArbitraryGeometryDefinitions
public import NLA.TR27.PaperGeneralHankelDefinitions
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

def parameterLift (D r : ℕ) : (Fin D → ℂ) →ₗ[ℂ] CurveSpace D where
  toFun w := Fin.cases 0 (fun j => (r : ℂ)⁻¹*w j)
  map_add' u v := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp [mul_add]
  map_smul' c w := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [mul_left_comm]

def parameterPolynomialLift (D r : ℕ) : Fin (D+1) → ImageCoordinatePolynomial D :=
  Fin.cases 0 (fun j => MvPolynomial.C ((r : ℂ)⁻¹)*MvPolynomial.X j)

def parameterRecoveryMatrix (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) :
    Matrix (Fin (r+2)) (Fin (r+2)) (ImageCoordinatePolynomial D) :=
  (centerHankel r a)⁻¹.map MvPolynomial.C *
    Matrix.of (fun i j => parameterPolynomialLift D r ⟨i.val+j.val,by omega⟩)

def parameterAffinePolynomial (D r : ℕ) (a : Fin r → ℂ) (j : Fin D) : Polynomial ℂ :=
  Polynomial.C (r : ℂ)*Polynomial.X^j.succ.val+
    Polynomial.C (projectionCenter D r (fun i => some (a i)) j.succ)

def parameterAlphaPolynomial (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) : Polynomial ℂ :=
  MvPolynomial.aeval (parameterAffinePolynomial D r a) (parameterRecoveryMatrix D r hD a).trace-
    Polynomial.C (((r+2 : ℕ) : ℂ)/(r : ℂ))

def parameterRecoveryV (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) : ImageCoordinatePolynomial D :=
  MvPolynomial.C ((r+2 : ℕ) : ℂ)*(parameterRecoveryMatrix D r hD a^2).trace-
    (parameterRecoveryMatrix D r hD a).trace^2

def parameterRecoveryW (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) : ImageCoordinatePolynomial D :=
  MvPolynomial.C (((r+2 : ℕ) : ℂ)^2)*(parameterRecoveryMatrix D r hD a^3).trace-
    MvPolynomial.C (3*((r+2 : ℕ) : ℂ))*(parameterRecoveryMatrix D r hD a).trace*
      (parameterRecoveryMatrix D r hD a^2).trace+
    MvPolynomial.C 2*(parameterRecoveryMatrix D r hD a).trace^3

def parameterBetaNumerator (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) : ImageCoordinatePolynomial D :=
  if parameterAlphaPolynomial D r hD a = 0 then (parameterRecoveryMatrix D r hD a).trace else
    (parameterRecoveryMatrix D r hD a).trace*MvPolynomial.C (r : ℂ)*parameterRecoveryV D r hD a-
      parameterRecoveryW D r hD a

def parameterBetaDenominator (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) : ImageCoordinatePolynomial D :=
  if parameterAlphaPolynomial D r hD a = 0 then MvPolynomial.C ((r+2 : ℕ) : ℂ) else
    MvPolynomial.C (((r+2 : ℕ) : ℂ)*(r : ℂ))*parameterRecoveryV D r hD a

def parameterRecoveryNumerator (D r : ℕ) (hD : 2*(r+1) ≤ D) (hr : 1 ≤ r) (a : Fin r → ℂ) :
    ImageCoordinatePolynomial D :=
  MvPolynomial.C ((r : ℂ)⁻¹)*MvPolynomial.X ⟨0,by omega⟩*parameterBetaDenominator D r hD a-
    MvPolynomial.C (projectionCenter D r (fun i => some (a i)) ⟨1,by omega⟩)*parameterBetaNumerator D r hD a

def parameterRecoveryDenominator (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) :
    ImageCoordinatePolynomial D := MvPolynomial.C (r : ℂ)*parameterBetaNumerator D r hD a

def parameterRecoveryException (D r : ℕ) (hD : 2*(r+1) ≤ D) (a : Fin r → ℂ) : Polynomial ℂ :=
  if parameterAlphaPolynomial D r hD a = 0 then 1 else parameterAlphaPolynomial D r hD a

end NLA.TR27.Paper
