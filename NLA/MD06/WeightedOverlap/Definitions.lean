module

public import NLA.MD06.BadSupportEnumeration.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WeightedOverlap
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open Reference.MD06BadJointMoments Reference.MD06JointSupportCounts
open Reference.MD06PairingCounts
open scoped BigOperators

def Overlaps {n q : ℕ} (f : JointDatum n q) : Prop :=
  ∃ i j : Fin q, i ≠ j ∧ ∃ u : Fin n,
    u ∈ VertexSupport (BadPattern (f i)) ∧ u ∈ VertexSupport (BadPattern (f j))

abbrev PartDatum (n q v e : ℕ) :=
  {f : JointDatum n q //
    (VertexSupport (JointPattern f)).card = v ∧
    (JointPattern f).card = e ∧ Overlaps f ∧ ∃ p : Pairing n, Matches (JointPattern f) p}

attribute [local instance] Classical.propDecidable

def PartCount (n q v e : ℕ) : ℕ :=
  ∑ f : PartDatum n q v e, PatternCount (JointPattern f.val)

def PartMean (n q v e : ℕ) : ℝ :=
  (PartCount n q v e : ℝ)/(Fintype.card (Pairing n) : ℝ)

end Reference.MD06WeightedOverlap
