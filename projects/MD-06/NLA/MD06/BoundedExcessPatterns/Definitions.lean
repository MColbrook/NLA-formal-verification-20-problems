module

public import NLA.MD06.MixedPatternShapes.Definitions
public import NLA.MD06.PairingCounts.ProductDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06BoundedExcess
open Reference.MD06CubicConfiguration Reference.MD06JointSupportCounts Reference.MD06PairingCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev ConstraintDatum (n v e : ℕ) :=
  {P : Finset (Dart n×Dart n) //
    (VertexSupport P).card=v ∧ P.card=e ∧
    (∀x∈P,x.1≠x.2) ∧
    ∀x∈P,∀y∈P,x≠y→Disjoint ({x.1,x.2} : Finset (Dart n)) {y.1,y.2}}
instance constraintDatumFintype (n v e : ℕ) : Fintype (ConstraintDatum n v e) :=
  Fintype.ofFinite _
def ConstraintCount (n v e : ℕ) : ℕ :=
  ∑P : ConstraintDatum n v e,PatternCount P.val
def ConstraintMean (n v e : ℕ) : ℝ :=
  (ConstraintCount n v e : ℝ)/(Fintype.card (Pairing n) : ℝ)

#print axioms constraintDatumFintype
end Reference.MD06BoundedExcess
