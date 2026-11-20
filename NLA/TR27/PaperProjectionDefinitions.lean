module

public import NLA.TR27.PaperCurveDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

def projectionCenter (D r : ℕ) (a : Fin r → Option ℂ) : CurveSpace D :=
  tangentVector D - ∑ i, curveVector D (a i)

def centerLine (D r : ℕ) (a : Fin r → Option ℂ) : Submodule ℂ (CurveSpace D) :=
  Submodule.span ℂ {projectionCenter D r a}

abbrev QuotientSpace (D r : ℕ) (a : Fin r → Option ℂ) := CurveSpace D ⧸ centerLine D r a

def quotientProjection (D r : ℕ) (a : Fin r → Option ℂ) :
    CurveSpace D →ₗ[ℂ] QuotientSpace D r a := (centerLine D r a).mkQ

def quotientCurve (D r : ℕ) (a : Fin r → Option ℂ) (t : Option ℂ) : QuotientSpace D r a :=
  quotientProjection D r a (curveVector D t)

def quotientTangent (D r : ℕ) (a : Fin r → Option ℂ) : QuotientSpace D r a :=
  quotientProjection D r a (tangentVector D)

def quotientPoints (D r : ℕ) (a : Fin r → Option ℂ) : Set (ℙ ℂ (QuotientSpace D r a)) :=
  {p | ∃ t : Option ℂ, Represents (quotientCurve D r a t) p}

def chosenParameters (r : ℕ) : Fin r → Option ℂ := fun i => some (((i : ℕ) + 1 : ℕ) : ℂ)

def familyDegree (r m : ℕ) : ℕ := r ^ m + r

end NLA.TR27.Paper
