module

public import NLA.MD06.CombinedDescendingMoments.JointDefinitions
public import Mathlib.Data.Fintype.CardEmbedding

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedPatternShapes Reference.MD06MixedLowCycleBijections
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06BadPatternCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_marked_joint_matching_iff {n q ell : ℕ} (F : MarkedJoint n q ell)
    (p : Pairing n) :
    Matches (MarkedJointPattern F) p ↔ ∀i,Matches (MarkedPattern (F i)) p := by
  constructor
  · intro h i e he
    apply h e
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,he⟩
  · intro h e he
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
    exact h i e hi

theorem actual_matched_marked_joint_card {n : ℕ} (q ell : ℕ) (p : Pairing n) :
    MatchedJointCount q ell p=(MarkedMatchingCount (ell:=ell) p).descFactorial q := by
  let e : {F : MarkedJoint n q ell // Matches (MarkedJointPattern F) p} ≃
      (Fin q↪{d : MarkedDatum n ell // Matches (MarkedPattern d) p}) :=
    { toFun := fun F =>
        { toFun := fun i => ⟨F.val i,(actual_marked_joint_matching_iff F.val p).mp F.property i⟩
          inj' := fun i j h => F.val.injective (congrArg Subtype.val h) }
      invFun := fun F =>
        ⟨{ toFun := fun i => (F i).val
           inj' := fun i j h => F.injective (Subtype.ext h) },
          (actual_marked_joint_matching_iff _ p).mpr (fun i => (F i).property)⟩
      left_inv := by intro F;apply Subtype.ext;ext i;rfl
      right_inv := by intro F;ext i;rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_embedding_eq,Fintype.card_fin] at h
  exact h

theorem actual_mean_descending_as_joint (n q ell : ℕ) :
    MeanDescending n q ell=MeanJoint n q ell := by
  unfold MeanDescending MeanJoint
  simp only [actual_matched_marked_joint_card]

#print axioms actual_marked_joint_matching_iff
#print axioms actual_matched_marked_joint_card
#print axioms actual_mean_descending_as_joint
end Reference.MD06CombinedMoments
