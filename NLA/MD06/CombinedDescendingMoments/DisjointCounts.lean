module

public import NLA.MD06.CombinedDescendingMoments.DisjointEquivalence
public import NLA.MD06.CanonicalDisjointTuples.TupleLimits

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedPatternShapes Reference.MD06CanonicalCyclePatterns
open Reference.MD06CanonicalDisjointTuples Reference.MD06SupportedCanonicalCycles
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
open Reference.MD06BadPatternCounts Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_disjoint_marked_count_sum {n : ℕ} (q ell : ℕ) (p : Pairing n) :
    DisjointMarkedCount q ell p=
      ∑mask : Fin q→MarkTag,TupleCount (fun i => TagLength ell (mask i)) p := by
  obtain ⟨E,hE⟩ := actual_disjoint_marked_tagged_pattern_equivalence
    (Finset.univ : Finset (Fin n)) q ell
  let e1 :
    {F : DisjointMarkedTuple (n:=n) Finset.univ q ell // Matches (MarkedUnion F.val) p} ≃
    {X : TaggedCycleTuple (n:=n) Finset.univ q ell // Matches (TupleUnion X.2) p} :=
    { toFun := fun F => ⟨E F.val,by rw [hE F.val];exact F.property⟩
      invFun := fun X => ⟨E.symm X.val,by
        have h := hE (E.symm X.val)
        rw [E.apply_symm_apply] at h
        rw [←h]
        exact X.property⟩
      left_inv := by intro F;apply Subtype.ext;exact E.symm_apply_apply F.val
      right_inv := by intro X;apply Subtype.ext;exact E.apply_symm_apply X.val }
  let e2 :
    {X : TaggedCycleTuple (n:=n) Finset.univ q ell // Matches (TupleUnion X.2) p} ≃
    (Σmask : Fin q→MarkTag,
      {C : CanonicalTuple (n:=n) Finset.univ (fun i => TagLength ell (mask i)) //
        Matches (TupleUnion C) p}) :=
    { toFun := fun X => ⟨X.val.1,⟨X.val.2,X.property⟩⟩
      invFun := fun X => ⟨⟨X.1,X.2.val⟩,X.2.property⟩
      left_inv := by rintro ⟨⟨mask,C⟩,hC⟩;rfl
      right_inv := by rintro ⟨mask,⟨C,hC⟩⟩;rfl }
  rw [DisjointMarkedCount,FamilyMatchingCount,Fintype.card_congr e1,
    Fintype.card_congr e2,Fintype.card_sigma]
  simp only [TupleCount,FamilyMatchingCount]

theorem actual_mean_disjoint_marked_sum (n q ell : ℕ) :
    MeanDisjointMarked n q ell=
      ∑mask : Fin q→MarkTag,MeanTuple n (fun i => TagLength ell (mask i)) := by
  have h : (∑p : Pairing n,(DisjointMarkedCount q ell p : ℝ))=
      ∑mask : Fin q→MarkTag,∑p : Pairing n,
        (TupleCount (fun i => TagLength ell (mask i)) p : ℝ) := by
    simp only [actual_disjoint_marked_count_sum,Nat.cast_sum]
    exact Finset.sum_comm
  unfold MeanDisjointMarked
  rw [h]
  simp only [MeanTuple,Finset.sum_div]

theorem actual_mean_disjoint_marked_shape_limit (q ell : ℕ) (hell : 0<ell) :
    Tendsto (fun k => MeanDisjointMarked (Size k) q ell) atTop
      (𝓝 (∑mask : Fin q→MarkTag,
        (2 : ℝ)^(CycleWeight (fun i => TagLength ell (mask i)))/
          (CycleSymmetryFactor (fun i => TagLength ell (mask i)) : ℝ))) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin q→MarkTag))
    (fun mask _ => actual_mean_canonical_disjoint_tuple_limit
      (fun i => TagLength ell (mask i)) (fun i => actual_tag_length_positive ell hell (mask i)))
  simpa only [actual_mean_disjoint_marked_sum] using h

#print axioms actual_disjoint_marked_count_sum
#print axioms actual_mean_disjoint_marked_sum
#print axioms actual_mean_disjoint_marked_shape_limit
end Reference.MD06CombinedMoments
