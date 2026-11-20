module

public import NLA.MD06.CanonicalDisjointTuples.HeadTailDefinitions
public import NLA.MD06.BadPatternCounts.CountDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalDisjointTuples
open Reference.MD06CubicConfiguration Reference.MD06BadPatternCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def TupleUnion {n q : ℕ} {S : Finset (Fin n)} {L : Fin q→ℕ}
    (F : CanonicalTuple S L) : Finset (Dart n×Dart n) := Finset.univ.biUnion F.val

def TupleCount {n q : ℕ} (L : Fin q→ℕ) (p : Pairing n) : ℕ :=
  FamilyMatchingCount (fun F : CanonicalTuple (n:=n) Finset.univ L => TupleUnion F) p

def MeanTuple {q : ℕ} (n : ℕ) (L : Fin q→ℕ) : ℝ :=
  (∑ p : Pairing n,(TupleCount L p : ℝ))/(Fintype.card (Pairing n) : ℝ)
end Reference.MD06CanonicalDisjointTuples
