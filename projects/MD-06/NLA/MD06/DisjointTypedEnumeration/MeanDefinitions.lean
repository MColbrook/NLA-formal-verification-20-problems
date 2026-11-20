module

public import NLA.MD06.DisjointTypedEnumeration.JointDefinitions
public import NLA.MD06.BadPatternCounts.CountDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06CubicConfiguration Reference.MD06BadJointMoments Reference.MD06BadPatternCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def TypedCount {n q : ℕ} (b : Fin q → Bool) (p : Pairing n) : ℕ :=
  FamilyMatchingCount (fun f : TypedJoint (n := n) Finset.univ b => JointPattern f.val) p

def MeanTyped {q : ℕ} (n : ℕ) (b : Fin q → Bool) : ℝ :=
  (∑ p : Pairing n,(TypedCount b p : ℝ))/(Fintype.card (Pairing n) : ℝ)
end Reference.MD06DisjointTypedEnumeration
