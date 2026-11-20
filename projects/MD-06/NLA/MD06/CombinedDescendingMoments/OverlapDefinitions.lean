module

public import NLA.MD06.CombinedDescendingMoments.DisjointDefinitions
public import NLA.MD06.MixedWeightedOverlap.TotalDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedWeightedOverlap Reference.MD06CubicConfiguration
open Reference.MD06BadPatternCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def JointOverlaps {n q ell : ℕ} (F : MarkedJoint n q ell) : Prop :=
  Overlaps (fun i => F i)

abbrev OverlappingJoint (n q ell : ℕ) := {F : MarkedJoint n q ell // JointOverlaps F}

abbrev NonoverlapJoint (n q ell : ℕ) := {F : MarkedJoint n q ell // ¬JointOverlaps F}

instance overlappingJointFintype (n q ell : ℕ) : Fintype (OverlappingJoint n q ell) :=
  Fintype.ofFinite _

instance nonoverlapJointFintype (n q ell : ℕ) : Fintype (NonoverlapJoint n q ell) :=
  Fintype.ofFinite _

def OverlapJointCount {n : ℕ} (q ell : ℕ) (p : Pairing n) : ℕ :=
  FamilyMatchingCount (fun F : OverlappingJoint n q ell => MarkedJointPattern F.val) p

def NonoverlapJointCount {n : ℕ} (q ell : ℕ) (p : Pairing n) : ℕ :=
  FamilyMatchingCount (fun F : NonoverlapJoint n q ell => MarkedJointPattern F.val) p

def MeanOverlapJoint (n q ell : ℕ) : ℝ :=
  (∑p : Pairing n,(OverlapJointCount q ell p : ℝ))/(Fintype.card (Pairing n) : ℝ)

#print axioms overlappingJointFintype
#print axioms nonoverlapJointFintype
end Reference.MD06CombinedMoments
