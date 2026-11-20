module

public import NLA.MD06.WeightedOverlap.TotalDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadDisjointDecomposition
open Reference.MD06CubicConfiguration Reference.MD06BadJointMoments
open Reference.MD06PairingCounts Reference.MD06WeightedOverlap
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def DisjointCount {n : ℕ} (q : ℕ) (p : Pairing n) : ℕ :=
  Fintype.card {f : JointDatum n q // ¬Overlaps f ∧ Matches (JointPattern f) p}

def MeanDisjoint (n q : ℕ) : ℝ :=
  (∑ p : Pairing n, (DisjointCount q p : ℝ))/(Fintype.card (Pairing n) : ℝ)

end Reference.MD06BadDisjointDecomposition
