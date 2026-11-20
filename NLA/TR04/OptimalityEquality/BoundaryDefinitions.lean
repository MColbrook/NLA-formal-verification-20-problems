module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual boundary-eigenspace projector definitions extending the checked real
MI-13 adaptation at e375a6fc0a12df52c4f5a38b53df78b837e1c390. -/
public import NLA.TR04.OptimalityEquality.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage

def leftBoundaryProjector {m n : ℕ} (A : Rect m n) (tau : ℝ) : Square m :=
  leftVectorMatrix A * Matrix.diagonal
    (fun i : Fin m => if singularValue A.transpose i.val = tau then (1 : ℝ) else 0) *
      (leftVectorMatrix A).transpose

end
end Reference.RealOptimalityEquality
