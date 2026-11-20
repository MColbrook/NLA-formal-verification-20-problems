module

public import NLA.MD06.DisjointTypedEnumeration.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06JointSupportCounts
open Reference.MD06BadJointMoments Reference.MD06WeightedOverlap

abbrev TypedJoint {n q : ℕ} (S : Finset (Fin n)) (b : Fin q → Bool) :=
  {f : JointDatum n q // ¬Overlaps f ∧ (∀i,IsDouble (f i)=b i) ∧
    ∀i,VertexSupport (BadPattern (f i)) ⊆ S}

abbrev DisjointJoint {n q : ℕ} (S : Finset (Fin n)) :=
  {f : JointDatum n q // ¬Overlaps f ∧ ∀i,VertexSupport (BadPattern (f i)) ⊆ S}
end Reference.MD06DisjointTypedEnumeration
