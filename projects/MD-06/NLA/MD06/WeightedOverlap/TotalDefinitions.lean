module

public import NLA.MD06.WeightedOverlap.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WeightedOverlap
open Reference.MD06CubicConfiguration Reference.MD06BadJointMoments Reference.MD06PairingCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def OverlapCount {n : ℕ} (q : ℕ) (p : Pairing n) : ℕ :=
  Fintype.card {f : JointDatum n q // Overlaps f ∧ Matches (JointPattern f) p}

def MeanOverlap (n q : ℕ) : ℝ :=
  ((∑ p : Pairing n, OverlapCount q p) : ℝ)/(Fintype.card (Pairing n) : ℝ)

end Reference.MD06WeightedOverlap
