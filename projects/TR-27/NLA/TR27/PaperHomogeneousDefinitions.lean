module

public import NLA.TR27.PaperCoordinateDefinitions
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.TR27.Paper

abbrev ImageCoordinatePolynomial (D : ℕ) := MvPolynomial (Fin D) ℂ
abbrev CurveParameterPolynomial := MvPolynomial (Fin 2) ℂ

def imageHomogeneousCoordinate (D r : ℕ) (hD : 2 ≤ D) (j : Fin D) :
    CurveParameterPolynomial :=
  MvPolynomial.C (chosenPivot r) * MvPolynomial.X 0 ^ (D-(retainedIndex D hD j).val) *
    MvPolynomial.X 1 ^ (retainedIndex D hD j).val -
  MvPolynomial.C (chosenPowerSum r (retainedIndex D hD j).val) *
    MvPolynomial.X 0 ^ (D-1) * MvPolynomial.X 1

def imageSubstitution (D r : ℕ) (hD : 2 ≤ D) :
    ImageCoordinatePolynomial D →ₐ[ℂ] CurveParameterPolynomial :=
  MvPolynomial.aeval (imageHomogeneousCoordinate D r hD)

def imageHomogeneousMap (D r : ℕ) (hD : 2 ≤ D) (u : Fin 2 → ℂ) : Fin D → ℂ :=
  fun j => MvPolynomial.eval u (imageHomogeneousCoordinate D r hD j)

def imageIdeal (D r : ℕ) (hD : 2 ≤ D) : Ideal (ImageCoordinatePolynomial D) :=
  RingHom.ker (imageSubstitution D r hD)

def coordinateParameterizedCone (D r : ℕ) (hD : 2 ≤ D) : Set (Fin D → ℂ) :=
  {w | w = 0 ∨ ∃ a : ℂ, a ≠ 0 ∧ ∃ t : Option ℂ, w = a • coordinateCurve D r hD t}

def quotientParameterizedCone (D r : ℕ) : Set (QuotientSpace D r (chosenParameters r)) :=
  {w | w = 0 ∨ ∃ a : ℂ, a ≠ 0 ∧ ∃ t : Option ℂ,
    w = a • quotientCurve D r (chosenParameters r) t}

end NLA.TR27.Paper
