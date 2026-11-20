module

public import NLA.TR27.PaperProjectionDefinitions
public import NLA.TR27.PaperHomogeneousDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

/-- Quotient coordinates eliminating coordinate zero, whose centre coefficient
is always -r. This avoids any nonvanishing assumption on a sum of parameters. -/
def parameterProjection (D r : ℕ) (a : Fin r → ℂ) : CurveSpace D →ₗ[ℂ] (Fin D → ℂ) where
  toFun w j := (r : ℂ)*w j.succ + projectionCenter D r (fun i => some (a i)) j.succ*w 0
  map_add' u v := by ext j; simp only [Pi.add_apply]; ring
  map_smul' c w := by ext j; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def parameterCoordinateCurve (D r : ℕ) (a : Fin r → ℂ) (t : Option ℂ) : Fin D → ℂ :=
  parameterProjection D r a (curveVector D t)

def parameterHomogeneousCoordinate (D r : ℕ) (a : Fin r → ℂ) (j : Fin D) :
    CurveParameterPolynomial :=
  MvPolynomial.C (r : ℂ) * MvPolynomial.X 0 ^ (D-j.succ.val) *
    MvPolynomial.X 1 ^ j.succ.val +
  MvPolynomial.C (projectionCenter D r (fun i => some (a i)) j.succ) * MvPolynomial.X 0 ^ D

def parameterSubstitution (D r : ℕ) (a : Fin r → ℂ) :
    ImageCoordinatePolynomial D →ₐ[ℂ] CurveParameterPolynomial :=
  MvPolynomial.aeval (parameterHomogeneousCoordinate D r a)

def parameterHomogeneousMap (D r : ℕ) (a : Fin r → ℂ) (u : Fin 2 → ℂ) : Fin D → ℂ :=
  fun j => MvPolynomial.eval u (parameterHomogeneousCoordinate D r a j)

def parameterImageIdeal (D r : ℕ) (a : Fin r → ℂ) : Ideal (ImageCoordinatePolynomial D) :=
  RingHom.ker (parameterSubstitution D r a)

end NLA.TR27.Paper
