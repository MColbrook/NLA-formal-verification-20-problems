module

public import NLA.MD06.MixedWeightedOverlap.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedWeightedOverlap
open Reference.MD06MixedPatternShapes Reference.MD06CubicConfiguration Reference.MD06PairingCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def OverlapCount {n : ℕ} (q ell : ℕ) (p : Pairing n) : ℕ :=
  Fintype.card {F : MarkedTuple n q ell // Overlaps F ∧ Matches (MarkedUnion F) p}

def MeanOverlap (n q ell : ℕ) : ℝ :=
  ((∑ p : Pairing n,OverlapCount q ell p) : ℝ)/(Fintype.card (Pairing n) : ℝ)
end Reference.MD06MixedWeightedOverlap
