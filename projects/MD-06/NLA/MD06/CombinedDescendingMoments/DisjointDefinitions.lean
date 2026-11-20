module

public import NLA.MD06.CombinedDescendingMoments.JointDefinitions
public import NLA.MD06.CanonicalDisjointTuples.MeanDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedPatternShapes Reference.MD06JointSupportCounts
open Reference.MD06CanonicalDisjointTuples Reference.MD06CubicConfiguration
open Reference.MD06BadPatternCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev DisjointMarkedTuple {n : ℕ} (S : Finset (Fin n)) (q ell : ℕ) :=
  {F : MarkedTuple n q ell //
    (∀i,VertexSupport (MarkedPattern (F i))⊆S) ∧
      ∀i j,i≠j→Disjoint (VertexSupport (MarkedPattern (F i)))
        (VertexSupport (MarkedPattern (F j)))}

abbrev TaggedCycleTuple {n : ℕ} (S : Finset (Fin n)) (q ell : ℕ) :=
  Σmask : Fin q→MarkTag,CanonicalTuple S (fun i => TagLength ell (mask i))

instance disjointMarkedTupleFintype {n : ℕ} (S : Finset (Fin n)) (q ell : ℕ) :
    Fintype (DisjointMarkedTuple S q ell) := Fintype.ofFinite _

instance taggedCycleTupleFintype {n : ℕ} (S : Finset (Fin n)) (q ell : ℕ) :
    Fintype (TaggedCycleTuple S q ell) := Fintype.ofFinite _

def DisjointMarkedCount {n : ℕ} (q ell : ℕ) (p : Pairing n) : ℕ :=
  FamilyMatchingCount (fun F : DisjointMarkedTuple (n:=n) Finset.univ q ell =>
    MarkedUnion F.val) p

def MeanDisjointMarked (n q ell : ℕ) : ℝ :=
  (∑p : Pairing n,(DisjointMarkedCount q ell p : ℝ))/(Fintype.card (Pairing n) : ℝ)

#print axioms disjointMarkedTupleFintype
#print axioms taggedCycleTupleFintype
end Reference.MD06CombinedMoments
