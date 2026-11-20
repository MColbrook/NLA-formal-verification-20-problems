module

public import NLA.MD06.SupportedCanonicalCycles.HeadDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalDisjointTuples
open Reference.MD06CanonicalCyclePatterns Reference.MD06CyclePairPatterns
open Reference.MD06CubicConfiguration Reference.MD06JointSupportCounts

abbrev CanonicalTuple {n q : ℕ} (S : Finset (Fin n)) (L : Fin q→ℕ) :=
  {F : Fin q→Finset (Dart n×Dart n) //
    (∀i,∃D : CycleData n (L i),CanonicalCyclePattern D=F i) ∧
      (∀i,VertexSupport (F i)⊆S) ∧
        ∀i j,i≠j→Disjoint (VertexSupport (F i)) (VertexSupport (F j))}

attribute [local instance] Classical.propDecidable

instance canonicalTupleFintype {n q : ℕ} (S : Finset (Fin n)) (L : Fin q→ℕ) :
    Fintype (CanonicalTuple S L) := Fintype.ofFinite _
#print axioms canonicalTupleFintype
end Reference.MD06CanonicalDisjointTuples
