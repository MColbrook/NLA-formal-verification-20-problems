module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual finite boundary multiplicities for the real MI-13 equality extension. -/
public import NLA.TR04.OptimalityEquality.BoundaryDefinitions

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage

def boundaryMultiplicity {m n : ℕ} (A : Rect m n) (tau : ℝ) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => singularValue A.transpose i.val = tau)).card

def retainedBoundaryMultiplicity {m n : ℕ} (A : Rect m n) (r : ℕ) : ℕ :=
  ((Finset.univ.filter (fun i : Fin m =>
    singularValue A.transpose i.val = singularValue A (r-1))).filter
      (fun i => i.val < r)).card

end
end Reference.RealOptimalityEquality
