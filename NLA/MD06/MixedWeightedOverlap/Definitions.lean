module

public import NLA.MD06.MixedPatternShapes.MarkedCycleDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedWeightedOverlap
open Reference.MD06MixedPatternShapes Reference.MD06JointSupportCounts
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts

def Overlaps {n q ell : ℕ} (F : MarkedTuple n q ell) : Prop :=
  ∃i j : Fin q,MarkedPattern (F i)≠MarkedPattern (F j)∧
    ∃u : Fin n,u∈VertexSupport (MarkedPattern (F i))∧u∈VertexSupport (MarkedPattern (F j))

abbrev PartDatum (n q ell v e : ℕ) :=
  {F : MarkedTuple n q ell //
    (VertexSupport (MarkedUnion F)).card=v∧(MarkedUnion F).card=e∧Overlaps F∧
      ∃p : Pairing n,Matches (MarkedUnion F) p}

attribute [local instance] Classical.propDecidable

noncomputable instance partDatumFintype (n q ell v e : ℕ) :
    Fintype (PartDatum n q ell v e) := Fintype.ofFinite _

def PartCount (n q ell v e : ℕ) : ℕ :=
  ∑F : PartDatum n q ell v e,PatternCount (MarkedUnion F.val)

def PartMean (n q ell v e : ℕ) : ℝ :=
  (PartCount n q ell v e : ℝ)/(Fintype.card (Pairing n) : ℝ)

#print axioms partDatumFintype
end Reference.MD06MixedWeightedOverlap
