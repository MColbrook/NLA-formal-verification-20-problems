module

public import NLA.MD06.DisjointTypedEnumeration.TypedMeans
public import NLA.MD06.WeightedOverlap.TotalCounts

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06DisjointTypedEnumeration
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open Reference.MD06BadJointMoments Reference.MD06BadPatternCounts Reference.MD06WeightedOverlap
open Reference.MD06BadDisjointDecomposition Reference.MD06FiniteProbability Reference.MD06PairingCounts
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_disjoint_count_typed_sum {n q : ℕ} (p : Pairing n) :
    DisjointCount q p = ∑ b : Fin q → Bool,TypedCount b p := by
  let e : {f : JointDatum n q // ¬Overlaps f ∧ Matches (JointPattern f) p} ≃
      (Σ b : Fin q → Bool,{f : TypedJoint Finset.univ b // Matches (JointPattern f.val) p}) :=
    { toFun := fun f => ⟨(fun i => IsDouble (f.val i)),
        ⟨⟨f.val,f.property.1,(fun _ => rfl),(fun _ => Finset.subset_univ _)⟩,f.property.2⟩⟩
      invFun := fun f => ⟨f.2.val.val,f.2.val.property.1,f.2.property⟩
      left_inv := by intro f;rfl
      right_inv := by
        rintro ⟨b,⟨⟨f,hn,hb,hs⟩,hm⟩⟩
        have he : (fun i => IsDouble (f i)) = b := funext hb
        subst b
        rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma] at h
  simpa only [DisjointCount,TypedCount,FamilyMatchingCount,Nat.card_eq_fintype_card] using h

theorem actual_mean_disjoint_typed_sum (n q : ℕ) :
    MeanDisjoint n q = ∑ b : Fin q → Bool,MeanTyped n b := by
  unfold MeanDisjoint MeanTyped
  simp_rw [actual_disjoint_count_typed_sum,Nat.cast_sum]
  rw [←Finset.sum_div,Finset.sum_comm]

theorem actual_mean_disjoint_limit (q : ℕ) :
    Tendsto (fun k : ℕ => MeanDisjoint (Size k) q) atTop (𝓝 ((2 : ℝ)^q)) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin q → Bool))
    (fun b _ => actual_mean_typed_limit b)
  have hc : (∑ _b : Fin q → Bool,(1 : ℝ)) = (2 : ℝ)^q := by
    simp
  rw [hc] at h
  exact h.congr (fun k => (actual_mean_disjoint_typed_sum (Size k) q).symm)

theorem actual_bad_descending_moment_limit (q : ℕ) :
    Tendsto (fun k : ℕ => MeanBadDescending k q) atTop (𝓝 ((2 : ℝ)^q)) := by
  have h := (actual_mean_disjoint_limit q).add (actual_weighted_overlap_mean_limit q)
  simpa only [actual_mean_bad_descending_disjoint_overlap,add_zero] using h

#print axioms actual_disjoint_count_typed_sum
#print axioms actual_mean_disjoint_typed_sum
#print axioms actual_mean_disjoint_limit
#print axioms actual_bad_descending_moment_limit
end Reference.MD06DisjointTypedEnumeration
