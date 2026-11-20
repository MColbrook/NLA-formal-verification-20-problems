module

public import NLA.MD06.BadDisjointDecomposition.Definitions
public import NLA.MD06.WeightedOverlap.TotalCounts
public import NLA.MD06.BadJointMoments.JointCounts

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadDisjointDecomposition
open Reference.MD06CubicConfiguration Reference.MD06BadJointMoments
open Reference.MD06Simplicity Reference.MD06BadPatternCounts
open Reference.MD06PairingCounts Reference.MD06WeightedOverlap Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_joint_count_disjoint_overlap {n q : ℕ} (p : Pairing n) :
    JointCount (q := q) p = DisjointCount q p + OverlapCount q p := by
  let split : {f : JointDatum n q // Matches (JointPattern f) p} ≃
      ({f : JointDatum n q // ¬Overlaps f ∧ Matches (JointPattern f) p} ⊕
       {f : JointDatum n q // Overlaps f ∧ Matches (JointPattern f) p}) :=
    { toFun := fun f => if h : Overlaps f.val then .inr ⟨f.val,h,f.property⟩
        else .inl ⟨f.val,h,f.property⟩
      invFun := fun f => match f with
        | .inl f => ⟨f.val,f.property.2⟩
        | .inr f => ⟨f.val,f.property.2⟩
      left_inv := by
        intro f
        by_cases h : Overlaps f.val
        · dsimp;rw [dif_pos h]
        · dsimp;rw [dif_neg h]
      right_inv := by
        intro f
        cases f with
        | inl f => dsimp;rw [dif_neg f.property.1]
        | inr f => dsimp;rw [dif_pos f.property.1] }
  have h := Fintype.card_congr split
  rw [Fintype.card_sum] at h
  simpa only [JointCount,FamilyMatchingCount,DisjointCount,OverlapCount,
    Nat.card_eq_fintype_card] using h

theorem actual_bad_descending_disjoint_overlap {n q : ℕ} (p : Pairing n) :
    (BadCount p).descFactorial q = DisjointCount q p + OverlapCount q p := by
  rw [← actual_joint_count_desc_factorial]
  exact actual_joint_count_disjoint_overlap p

theorem actual_mean_bad_descending_disjoint_overlap (k q : ℕ) :
    MeanBadDescending k q = MeanDisjoint (Size k) q + MeanOverlap (Size k) q := by
  unfold MeanBadDescending MeanDisjoint MeanOverlap
  simp_rw [actual_bad_descending_disjoint_overlap,Nat.cast_add]
  rw [Finset.sum_add_distrib,add_div]

theorem actual_no_overlap_small_order {n q : ℕ} (f : JointDatum n q) (hq : q ≤ 1) :
    ¬Overlaps f := by
  rintro ⟨i,j,hij,u,hi,hj⟩
  have h : i = j := by apply Fin.ext;omega
  exact hij h

theorem actual_overlap_count_small_order {n q : ℕ} (p : Pairing n) (hq : q ≤ 1) :
    OverlapCount q p = 0 := by
  let : IsEmpty {f : JointDatum n q // Overlaps f ∧ Matches (JointPattern f) p} :=
    ⟨fun f => actual_no_overlap_small_order f.val hq f.property.1⟩
  simp [OverlapCount]

theorem actual_mean_overlap_small_order (n q : ℕ) (hq : q ≤ 1) :
    MeanOverlap n q = 0 := by
  simp only [MeanOverlap,actual_overlap_count_small_order (hq := hq),
    Nat.cast_zero,Finset.sum_const_zero,zero_div]

theorem actual_mean_disjoint_zero (k : ℕ) : MeanDisjoint (Size k) 0 = 1 := by
  have h := actual_mean_bad_descending_disjoint_overlap k 0
  rw [actual_mean_bad_descending_zero,actual_mean_overlap_small_order (Size k) 0 (by omega),
    add_zero] at h
  exact h.symm

theorem actual_mean_disjoint_one (k : ℕ) : MeanDisjoint (Size k) 1 = MeanBadCount k := by
  have h := actual_mean_bad_descending_disjoint_overlap k 1
  rw [actual_mean_bad_descending_one,actual_mean_overlap_small_order (Size k) 1 (by omega),
    add_zero] at h
  exact h.symm

theorem actual_mean_disjoint_one_limit :
    Tendsto (fun k : ℕ => MeanDisjoint (Size k) 1) atTop (𝓝 (2 : ℝ)) := by
  simpa only [actual_mean_disjoint_one] using actual_mean_bad_count_limit

theorem actual_no_overlap_iff_vertex_disjoint {n q : ℕ} (f : JointDatum n q) :
    ¬Overlaps f ↔ ∀ i j : Fin q, i ≠ j →
      Disjoint (Reference.MD06JointSupportCounts.VertexSupport (BadPattern (f i)))
        (Reference.MD06JointSupportCounts.VertexSupport (BadPattern (f j))) := by
  constructor
  · intro h i j hij
    apply Finset.disjoint_left.mpr
    intro u hi hj
    exact h ⟨i,j,hij,u,hi,hj⟩
  · intro h ho
    rcases ho with ⟨i,j,hij,u,hi,hj⟩
    exact Finset.disjoint_left.mp (h i j hij) hi hj

#print axioms actual_no_overlap_iff_vertex_disjoint

#print axioms actual_joint_count_disjoint_overlap
#print axioms actual_bad_descending_disjoint_overlap
#print axioms actual_mean_bad_descending_disjoint_overlap
#print axioms actual_no_overlap_small_order
#print axioms actual_overlap_count_small_order
#print axioms actual_mean_overlap_small_order
#print axioms actual_mean_disjoint_zero
#print axioms actual_mean_disjoint_one
#print axioms actual_mean_disjoint_one_limit
end Reference.MD06BadDisjointDecomposition
