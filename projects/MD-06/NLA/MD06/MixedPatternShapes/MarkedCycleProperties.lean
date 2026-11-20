module

public import NLA.MD06.MixedPatternShapes.MarkedCycleDefinitions
public import NLA.MD06.MixedPatternShapes.BadCycleProperties
public import NLA.MD06.CanonicalCycleOverlap.Excess

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedPatternShapes
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06Simplicity Reference.MD06CanonicalCycleOverlap Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

theorem actual_marked_cycle_pattern {n ell : ℕ} (d : MarkedDatum n ell) :
    CanonicalCyclePattern (MarkedCycle d)=MarkedPattern d := by
  cases d with
  | inl b => exact actual_bad_canonical_cycle b
  | inr C => exact Classical.choose_spec C.property

theorem actual_marked_length_bound {n ell : ℕ} (d : MarkedDatum n ell) :
    MarkedLength d≤max 2 ell := by
  cases d with
  | inl b => exact (actual_bad_length_bounds b).2.trans (Nat.le_max_left _ _)
  | inr C => exact Nat.le_max_right _ _

theorem actual_marked_length_positive {n ell : ℕ} (h : 0<ell) (d : MarkedDatum n ell) :
    0<MarkedLength d := by
  cases d with
  | inl b => exact lt_of_lt_of_le (by decide : 0<1) (actual_bad_length_bounds b).1
  | inr C => exact h

theorem actual_marked_union_as_cycle_family {n q ell : ℕ} (F : MarkedTuple n q ell) :
    MarkedUnion F=FamilyUnion (fun i => MarkedLength (F i)) (fun i => MarkedCycle (F i)) := by
  ext e
  simp only [MarkedUnion,FamilyUnion,Finset.mem_biUnion,Finset.mem_univ,true_and,
    actual_marked_cycle_pattern]

theorem actual_marked_union_edge_bound {n q ell : ℕ} (F : MarkedTuple n q ell) :
    (MarkedUnion F).card≤q*(max 2 ell) := by
  rw [actual_marked_union_as_cycle_family]
  apply (actual_family_cycle_edge_card_bound
    (fun i => MarkedLength (F i)) (fun i => MarkedCycle (F i))).trans
  have hsum : (∑i : Fin q,MarkedLength (F i))≤∑_ : Fin q,max 2 ell := by
    apply Finset.sum_le_sum
    intro i _
    exact actual_marked_length_bound (F i)
  simpa using hsum

theorem actual_mixed_marked_overlap_excess {n q ell : ℕ} (F : MarkedTuple n q ell)
    (p : Pairing n) (hp : Matches (MarkedUnion F) p)
    (i j : Fin q) (hne : MarkedPattern (F i)≠MarkedPattern (F j))
    (hov : ∃u,u∈VertexSupport (MarkedPattern (F i))∧
      u∈VertexSupport (MarkedPattern (F j))) :
    (VertexSupport (MarkedUnion F)).card+1≤(MarkedUnion F).card := by
  have hraw := actual_family_cycle_overlap_support_bound
    (fun k => MarkedLength (F k)) (fun k => MarkedCycle (F k)) p
    ((actual_marked_union_as_cycle_family F) ▸ hp) i j
    (by simpa only [actual_marked_cycle_pattern] using hne)
    (by simpa only [actual_marked_cycle_pattern] using (Finset.not_disjoint_iff.mpr hov))
  simpa only [←actual_marked_union_as_cycle_family F] using hraw.1

theorem actual_mixed_marked_overlap_bounded_excess {n q ell : ℕ} (F : MarkedTuple n q ell)
    (p : Pairing n) (hp : Matches (MarkedUnion F) p)
    (i j : Fin q) (hne : MarkedPattern (F i)≠MarkedPattern (F j))
    (hov : ∃u,u∈VertexSupport (MarkedPattern (F i))∧
      u∈VertexSupport (MarkedPattern (F j))) :
    (VertexSupport (MarkedUnion F)).card+1≤(MarkedUnion F).card∧
      (MarkedUnion F).card≤q*(max 2 ell) :=
  ⟨actual_mixed_marked_overlap_excess F p hp i j hne hov,
    actual_marked_union_edge_bound F⟩

#print axioms actual_marked_cycle_pattern
#print axioms actual_marked_length_bound
#print axioms actual_marked_length_positive
#print axioms actual_marked_union_as_cycle_family
#print axioms actual_marked_union_edge_bound
#print axioms actual_mixed_marked_overlap_excess
#print axioms actual_mixed_marked_overlap_bounded_excess
end Reference.MD06MixedPatternShapes
