module

public import NLA.MD06.CombinedDescendingMoments.Definitions
public import NLA.MD06.BadPatternCounts.CountDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedPatternShapes Reference.MD06MixedLowCycleBijections
open Reference.MD06BadPatternCounts Reference.MD06CubicConfiguration
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev MarkedJoint (n q ell : ℕ) := Fin q↪MarkedDatum n ell

instance markedJointFintype (n q ell : ℕ) : Fintype (MarkedJoint n q ell) :=
  Fintype.ofFinite _

def MarkedJointPattern {n q ell : ℕ} (F : MarkedJoint n q ell) :
    Finset (Dart n×Dart n) := MarkedUnion (fun i => F i)

def MatchedJointCount {n : ℕ} (q ell : ℕ) (p : Pairing n) : ℕ :=
  FamilyMatchingCount (fun F : MarkedJoint n q ell => MarkedJointPattern F) p

def MeanJoint (n q ell : ℕ) : ℝ :=
  (∑ p : Pairing n,(MatchedJointCount q ell p : ℝ))/(Fintype.card (Pairing n) : ℝ)

def MeanDescending (n q ell : ℕ) : ℝ :=
  (∑ p : Pairing n,((MarkedMatchingCount (ell:=ell) p).descFactorial q : ℝ))/
    (Fintype.card (Pairing n) : ℝ)

#print axioms markedJointFintype
end Reference.MD06CombinedMoments
