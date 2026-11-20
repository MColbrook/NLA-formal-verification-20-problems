module

public import NLA.MD06.CombinedDescendingMoments.DisjointDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06SupportedCanonicalCycles
open scoped BigOperators

def TagWeight (ell : ℕ) (t : MarkTag) : ℝ :=
  (2 : ℝ)^(TagLength ell t)/(2*(TagLength ell t : ℝ))

def LeadingConstant (q ell : ℕ) : ℝ :=
  ∑mask : Fin q→MarkTag,(2 : ℝ)^(CycleWeight (fun i => TagLength ell (mask i)))/
    (CycleSymmetryFactor (fun i => TagLength ell (mask i)) : ℝ)
end Reference.MD06CombinedMoments
