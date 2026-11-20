module

public import NLA.MD06.MixedWeightedOverlap.TotalDefinitions
public import NLA.MD06.MixedWeightedOverlap.PartLimits

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedWeightedOverlap
open Reference.MD06MixedPatternShapes Reference.MD06JointSupportCounts
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
open Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_mixed_overlapping_tuple_support_bound {n q ell : ℕ}
    (F : MarkedTuple n q ell) (p : Pairing n) (hp : Matches (MarkedUnion F) p)
    (hO : Overlaps F) :
    (VertexSupport (MarkedUnion F)).card+1≤(MarkedUnion F).card ∧
      (MarkedUnion F).card≤q*(max 2 ell) := by
  obtain ⟨i,j,hne,hov⟩ := hO
  exact actual_mixed_marked_overlap_bounded_excess F p hp i j hne hov

theorem actual_mixed_overlap_count_shape_sum (n q ell : ℕ) :
    (∑ p : Pairing n,OverlapCount q ell p)=
      ∑ v : Fin (q*(max 2 ell)+1),∑ e : Fin (q*(max 2 ell)+1),
        PartCount n q ell v.val e.val := by
  let equiv :
    (Σ p : Pairing n,{F : MarkedTuple n q ell // Overlaps F ∧ Matches (MarkedUnion F) p}) ≃
    (Σ v : Fin (q*(max 2 ell)+1),Σ e : Fin (q*(max 2 ell)+1),
      Σ F : PartDatum n q ell v.val e.val,{p : Pairing n // Matches (MarkedUnion F.val) p}) :=
    { toFun := fun x =>
        let hb := actual_mixed_overlapping_tuple_support_bound x.2.val x.1
          x.2.property.2 x.2.property.1
        ⟨⟨(VertexSupport (MarkedUnion x.2.val)).card,by omega⟩,
          ⟨(MarkedUnion x.2.val).card,by omega⟩,
          ⟨x.2.val,rfl,rfl,x.2.property.1,⟨x.1,x.2.property.2⟩⟩,
          ⟨x.1,x.2.property.2⟩⟩
      invFun := fun x =>
        ⟨x.2.2.2.val,⟨x.2.2.1.val,x.2.2.1.property.2.2.1,x.2.2.2.property⟩⟩
      left_inv := by rintro ⟨p,F,hF⟩;rfl
      right_inv := by
        rintro ⟨⟨v,hv⟩,⟨e,he⟩,⟨F,hFv,hFe,hFO,hFC⟩,⟨p,hp⟩⟩
        dsimp at hFv hFe
        subst v
        subst e
        rfl }
  have h := Fintype.card_congr equiv
  simp only [Fintype.card_sigma] at h
  simpa only [OverlapCount,PartCount,PatternCount,Nat.card_eq_fintype_card] using h

theorem actual_mixed_mean_overlap_shape_sum (n q ell : ℕ) :
    MeanOverlap n q ell=
      ∑ v : Fin (q*(max 2 ell)+1),∑ e : Fin (q*(max 2 ell)+1),
        PartMean n q ell v.val e.val := by
  have h : (∑ p : Pairing n,(OverlapCount q ell p : ℝ))=
      ∑ v : Fin (q*(max 2 ell)+1),∑ e : Fin (q*(max 2 ell)+1),
        (PartCount n q ell v.val e.val : ℝ) := by
    exact_mod_cast actual_mixed_overlap_count_shape_sum n q ell
  unfold MeanOverlap
  rw [h]
  simp only [PartMean,Finset.sum_div]

theorem actual_mixed_weighted_overlap_mean_limit (q ell : ℕ) :
    Tendsto (fun k => MeanOverlap (Size k) q ell) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin (q*(max 2 ell)+1)))
    (fun v _ => tendsto_finsetSum (Finset.univ : Finset (Fin (q*(max 2 ell)+1)))
      (fun e _ => actual_mixed_part_mean_all_shapes_limit q ell v.val e.val))
  simpa only [actual_mixed_mean_overlap_shape_sum,Finset.sum_const_zero] using h

#print axioms actual_mixed_overlapping_tuple_support_bound
#print axioms actual_mixed_overlap_count_shape_sum
#print axioms actual_mixed_mean_overlap_shape_sum
#print axioms actual_mixed_weighted_overlap_mean_limit
end Reference.MD06MixedWeightedOverlap
