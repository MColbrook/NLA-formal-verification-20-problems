module

public import NLA.MD06.SimplicityBonferroni.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadPatternCounts
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06FiniteProbability
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def FamilyMatchingCount {I : Type*} [Fintype I] {n : ℕ}
    (C : I → Finset (Dart n × Dart n)) (p : Pairing n) : ℕ :=
  Fintype.card {i : I // Matches (C i) p}

abbrev LoopCount {n : ℕ} (p : Pairing n) := FamilyMatchingCount LoopPattern p
abbrev DoubleCount {n : ℕ} (p : Pairing n) := FamilyMatchingCount DoublePattern p

noncomputable def MeanLoopCount (k : ℕ) : ℝ :=
  (∑ p : Pairing (Size k), (LoopCount p : ℝ)) / Fintype.card (Pairing (Size k))
noncomputable def MeanDoubleCount (k : ℕ) : ℝ :=
  (∑ p : Pairing (Size k), (DoubleCount p : ℝ)) / Fintype.card (Pairing (Size k))
noncomputable def MeanBadCount (k : ℕ) : ℝ :=
  (∑ p : Pairing (Size k), (BadCount p : ℝ)) / Fintype.card (Pairing (Size k))

end Reference.MD06BadPatternCounts