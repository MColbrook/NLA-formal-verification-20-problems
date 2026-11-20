module

public import NLA.MD06.SupportedCanonicalCycles.Definitions
public import NLA.MD06.BadSupportEnumeration.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedPatternShapes
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06Simplicity Reference.MD06SupportedCanonicalCycles

def LocalDarts {n : ℕ} (S : Finset (Fin n)) : Finset (Dart n) :=
  S.product (Finset.univ : Finset (Fin 3))

def LocalEdges {n : ℕ} (S : Finset (Fin n)) : Finset (Dart n×Dart n) :=
  (LocalDarts S).product (LocalDarts S)

abbrev ConstraintOn {n : ℕ} (S : Finset (Fin n)) :=
  {C : Finset (Dart n×Dart n) // VertexSupport C⊆S}

abbrev MarkedDatum (n ell : ℕ) := BadDatum n⊕CanonicalCycleDatum n ell

def MarkedPattern {n ell : ℕ} (d : MarkedDatum n ell) : Finset (Dart n×Dart n) :=
  match d with
  | .inl b => BadPattern b
  | .inr C => C.val

abbrev MarkedTuple (n q ell : ℕ) := Fin q→MarkedDatum n ell

def MarkedUnion {n q ell : ℕ} (F : MarkedTuple n q ell) : Finset (Dart n×Dart n) :=
  Finset.univ.biUnion (fun i => MarkedPattern (F i))

abbrev SupportedMarked {n : ℕ} (S : Finset (Fin n)) (ell : ℕ) :=
  {d : MarkedDatum n ell // VertexSupport (MarkedPattern d)⊆S}

abbrev SupportedMarkedTuple {n : ℕ} (S : Finset (Fin n)) (q ell : ℕ) :=
  {F : MarkedTuple n q ell // VertexSupport (MarkedUnion F)⊆S}

attribute [local instance] Classical.propDecidable

noncomputable instance markedDatumFintype (n ell : ℕ) : Fintype (MarkedDatum n ell) :=
  Fintype.ofFinite _

noncomputable instance markedTupleFintype (n q ell : ℕ) : Fintype (MarkedTuple n q ell) :=
  Fintype.ofFinite _

noncomputable instance supportedMarkedFintype {n : ℕ} (S : Finset (Fin n)) (ell : ℕ) :
    Fintype (SupportedMarked S ell) := Fintype.ofFinite _

noncomputable instance supportedMarkedTupleFintype {n : ℕ} (S : Finset (Fin n)) (q ell : ℕ) :
    Fintype (SupportedMarkedTuple S q ell) := Fintype.ofFinite _

#print axioms markedDatumFintype
#print axioms markedTupleFintype
#print axioms supportedMarkedFintype
#print axioms supportedMarkedTupleFintype
end Reference.MD06MixedPatternShapes
