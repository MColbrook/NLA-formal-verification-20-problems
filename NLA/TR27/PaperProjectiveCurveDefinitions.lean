module

public import NLA.TR27.PaperProjectiveTopologyDefinitions
public import NLA.TR27.PaperImageGeometry

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

/-- The actual degree-D homogeneous parametrization on the standard
projective line. Nonvanishing follows from the previously checked no-basepoint theorem. -/
def projectiveCurveMap (D r : ℕ) (hD : 2 ≤ D) (hr : 3 ≤ r)
    (p : ℙ ℂ (Fin 2 → ℂ)) : ℙ ℂ (Fin D → ℂ) :=
  Projectivization.mk ℂ (imageHomogeneousMap D r hD p.rep)
    (fun h => p.rep_nonzero ((imageHomogeneousMap_eq_zero_iff D r hD hr p.rep).mp h))

end NLA.TR27.Paper
