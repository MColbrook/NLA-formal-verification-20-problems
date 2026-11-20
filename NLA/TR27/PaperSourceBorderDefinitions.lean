module

public import NLA.TR27.PaperHankelPolynomialDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

/-- Projective Zariski closure in the actual source homogeneous coordinates.
This is the same all-homogeneous-polynomial semantics as ProjectiveVariety.zariskiClosure. -/
def sourceProjectiveClosure (D : ℕ) (Y : Set (ℙ ℂ (CurveSpace D))) :
    Set (ℙ ℂ (CurveSpace D)) :=
  {p | ∀ (f : MvPolynomial (Fin (D+1)) ℂ) (d : ℕ), f.IsHomogeneous d →
    (∀ q ∈ Y, MvPolynomial.eval q.rep f = 0) → MvPolynomial.eval p.rep f = 0}

def sourceBorderRank (D : ℕ) (p : ℙ ℂ (CurveSpace D)) : ℕ :=
  sInf {k | p ∈ sourceProjectiveClosure D {q | ProjectiveRankAtMost (curvePoints D) k q}}

def secantSlope (D : ℕ) (t : ℂ) : CurveSpace D :=
  fun j => if j.val = 0 then 0 else t^(j.val-1)

def centerDegeneration (D r : ℕ) (a : Fin r → ℂ) (t : ℂ) : CurveSpace D :=
  secantSlope D t - ∑ i, curveVector D (some (a i))

end NLA.TR27.Paper
