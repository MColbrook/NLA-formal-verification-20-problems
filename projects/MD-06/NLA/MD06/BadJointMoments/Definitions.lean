module

public import NLA.MD06.BadPatternCounts.CountDefinitions
public import Mathlib.Data.Fintype.CardEmbedding

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadJointMoments
open Reference.MD06Simplicity Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06FiniteProbability Reference.MD06BadPatternCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev JointDatum (n q : ℕ) := Fin q ↪ BadDatum n

def JointPattern {n q : ℕ} (f : JointDatum n q) : Finset (Dart n × Dart n) :=
  Finset.univ.biUnion (fun i : Fin q => BadPattern (f i))

abbrev JointCount {n q : ℕ} (p : Pairing n) :=
  FamilyMatchingCount (JointPattern (q := q)) p

noncomputable def MeanBadDescending (k q : ℕ) : ℝ :=
  (∑ p : Pairing (Size k), ((BadCount p).descFactorial q : ℝ)) /
    Fintype.card (Pairing (Size k))

noncomputable def MeanBadChoose (k q : ℕ) : ℝ :=
  (∑ p : Pairing (Size k), ((BadCount p).choose q : ℝ)) /
    Fintype.card (Pairing (Size k))

end Reference.MD06BadJointMoments
