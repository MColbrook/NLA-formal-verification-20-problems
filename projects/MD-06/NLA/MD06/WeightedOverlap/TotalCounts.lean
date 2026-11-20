module

public import NLA.MD06.WeightedOverlap.TotalDefinitions
public import NLA.MD06.WeightedOverlap.PartLimits

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WeightedOverlap
open Reference.MD06CubicConfiguration Reference.MD06BadJointMoments Reference.MD06PairingCounts
open Reference.MD06JointSupportCounts Reference.MD06BadOverlap Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_overlap_count_shape_sum (n q : ℕ) :
    (∑ p : Pairing n, OverlapCount q p) =
      ∑ v : Fin (2*q+1), ∑ e : Fin (2*q+1), PartCount n q v.val e.val := by
  let equiv :
      (Σ p : Pairing n, {f : JointDatum n q // Overlaps f ∧ Matches (JointPattern f) p}) ≃
      (Σ v : Fin (2*q+1), Σ e : Fin (2*q+1),
        Σ f : PartDatum n q v.val e.val, {p : Pairing n // Matches (JointPattern f.val) p}) :=
    { toFun := fun x =>
        let hb := actual_overlapping_joint_support_bound x.2.val x.1
          x.2.property.2 x.2.property.1
        ⟨⟨(VertexSupport (JointPattern x.2.val)).card,by omega⟩,
         ⟨(JointPattern x.2.val).card,by omega⟩,
         ⟨x.2.val,rfl,rfl,x.2.property.1,⟨x.1,x.2.property.2⟩⟩,
         ⟨x.1,x.2.property.2⟩⟩
      invFun := fun x => ⟨x.2.2.2.val,
        ⟨x.2.2.1.val,x.2.2.1.property.2.2.1,x.2.2.2.property⟩⟩
      left_inv := by rintro ⟨p,f,hf⟩;rfl
      right_inv := by
        rintro ⟨⟨v,hv⟩,⟨e,he⟩,⟨f,hfv,hfe,hfo,hfc⟩,⟨p,hp⟩⟩
        dsimp at hfv hfe
        subst v
        subst e
        rfl }
  have h := Fintype.card_congr equiv
  simp only [Fintype.card_sigma] at h
  simpa only [OverlapCount,PartCount,PatternCount,Nat.card_eq_fintype_card] using h

theorem actual_mean_overlap_shape_sum (n q : ℕ) :
    MeanOverlap n q =
      ∑ v : Fin (2*q+1), ∑ e : Fin (2*q+1), PartMean n q v.val e.val := by
  have h : (∑ p : Pairing n, (OverlapCount q p : ℝ)) =
      ∑ v : Fin (2*q+1), ∑ e : Fin (2*q+1), (PartCount n q v.val e.val : ℝ) := by
    exact_mod_cast actual_overlap_count_shape_sum n q
  unfold MeanOverlap
  rw [h]
  simp only [PartMean,Finset.sum_div]

theorem actual_weighted_overlap_mean_limit (q : ℕ) :
    Tendsto (fun k : ℕ => MeanOverlap (Size k) q) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin (2*q+1)))
    (fun v _ => tendsto_finsetSum (Finset.univ : Finset (Fin (2*q+1)))
      (fun e _ => actual_part_mean_all_shapes_limit q v.val e.val))
  simpa only [actual_mean_overlap_shape_sum,Finset.sum_const_zero] using h

#print axioms actual_overlap_count_shape_sum
#print axioms actual_mean_overlap_shape_sum
#print axioms actual_weighted_overlap_mean_limit
end Reference.MD06WeightedOverlap
