module

public import NLA.MD06.CombinedDescendingMoments.OverlapGeometry
public import NLA.MD06.CombinedDescendingMoments.JointCardinality

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedPatternShapes Reference.MD06MixedWeightedOverlap
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06BadPatternCounts
attribute [local instance] Classical.propDecidable

theorem actual_joint_count_partition {n : ℕ} (q ell : ℕ) (p : Pairing n) :
    MatchedJointCount q ell p=NonoverlapJointCount q ell p+OverlapJointCount q ell p := by
  let E : {F : MarkedJoint n q ell // Matches (MarkedJointPattern F) p} ≃
      ({F : NonoverlapJoint n q ell // Matches (MarkedJointPattern F.val) p} ⊕
       {F : OverlappingJoint n q ell // Matches (MarkedJointPattern F.val) p}) :=
    { toFun := fun F => if h : JointOverlaps F.val then
          Sum.inr ⟨⟨F.val,h⟩,F.property⟩ else Sum.inl ⟨⟨F.val,h⟩,F.property⟩
      invFun := fun X => match X with
        | Sum.inl F => ⟨F.val.val,F.property⟩
        | Sum.inr F => ⟨F.val.val,F.property⟩
      left_inv := by intro F;by_cases h : JointOverlaps F.val <;> simp [h]
      right_inv := by
        intro X
        cases X with
        | inl F => simp [F.val.property]
        | inr F => simp [F.val.property] }
  exact (Fintype.card_congr E).trans Fintype.card_sum

theorem actual_nonoverlap_joint_count_eq_disjoint {n : ℕ} (q ell : ℕ)
    (hell : 3≤ell) (p : Pairing n) :
    NonoverlapJointCount q ell p=DisjointMarkedCount q ell p := by
  let E : NonoverlapJoint n q ell ≃ DisjointMarkedTuple (n:=n) Finset.univ q ell :=
    { toFun := fun F => ⟨fun i => F.val i,⟨fun _ => Finset.subset_univ _,
          (actual_nonoverlap_joint_iff_vertex_disjoint hell F.val).mp F.property⟩⟩
      invFun := fun F => ⟨⟨F.val,actual_disjoint_marked_tuple_injective Finset.univ
          (by omega) F⟩,(actual_nonoverlap_joint_iff_vertex_disjoint hell _).mpr F.property.2⟩
      left_inv := by intro F;apply Subtype.ext;apply Function.Embedding.ext;intro i;rfl
      right_inv := by intro F;apply Subtype.ext;rfl }
  let E' : {F : NonoverlapJoint n q ell // Matches (MarkedJointPattern F.val) p} ≃
      {F : DisjointMarkedTuple (n:=n) Finset.univ q ell // Matches (MarkedUnion F.val) p} :=
    { toFun := fun F => ⟨E F.val,F.property⟩
      invFun := fun F => ⟨E.symm F.val,F.property⟩
      left_inv := by intro F;apply Subtype.ext;exact E.symm_apply_apply F.val
      right_inv := by intro F;apply Subtype.ext;exact E.apply_symm_apply F.val }
  exact Fintype.card_congr E'

theorem actual_overlap_joint_count_le {n : ℕ} (q ell : ℕ) (p : Pairing n) :
    OverlapJointCount q ell p≤OverlapCount q ell p := by
  let f : {F : OverlappingJoint n q ell // Matches (MarkedJointPattern F.val) p} →
      {F : MarkedTuple n q ell // Overlaps F ∧ Matches (MarkedUnion F) p} :=
    fun F => ⟨fun i => F.val.val i,F.val.property,F.property⟩
  have hf : Function.Injective f := by
    intro F G h
    apply Subtype.ext
    apply Subtype.ext
    apply Function.Embedding.ext
    intro i
    exact congrFun (congrArg Subtype.val h) i
  exact Fintype.card_le_of_injective f hf

theorem actual_joint_count_disjoint_overlap {n : ℕ} (q ell : ℕ)
    (hell : 3≤ell) (p : Pairing n) :
    MatchedJointCount q ell p=DisjointMarkedCount q ell p+OverlapJointCount q ell p := by
  rw [actual_joint_count_partition,actual_nonoverlap_joint_count_eq_disjoint q ell hell p]

#print axioms actual_joint_count_partition
#print axioms actual_nonoverlap_joint_count_eq_disjoint
#print axioms actual_overlap_joint_count_le
#print axioms actual_joint_count_disjoint_overlap
end Reference.MD06CombinedMoments
