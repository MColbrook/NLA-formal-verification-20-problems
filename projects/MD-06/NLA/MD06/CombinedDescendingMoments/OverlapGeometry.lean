module

public import NLA.MD06.CombinedDescendingMoments.OverlapDefinitions
public import NLA.MD06.CombinedDescendingMoments.TagProperties
public import NLA.MD06.MixedLowCycleBijections.MarkedBinding
public import NLA.MD06.JointSupportCounts.SupportProperties

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedPatternShapes Reference.MD06MixedLowCycleBijections
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_marked_pattern_card_positive {n ell : ℕ} (hell : 0<ell)
    (d : MarkedDatum n ell) : 0<(MarkedPattern d).card := by
  rw [←actual_marked_to_tagged_pattern d]
  change 0<((MarkedToTagged d).2.val).card
  rw [actual_canonical_datum_edge_card]
  exact actual_tag_length_positive ell hell (MarkedToTagged d).1

theorem actual_marked_vertex_support_nonempty {n ell : ℕ} (hell : 0<ell)
    (d : MarkedDatum n ell) : (VertexSupport (MarkedPattern d)).Nonempty := by
  obtain ⟨e,he⟩ := Finset.card_pos.mp (actual_marked_pattern_card_positive hell d)
  exact ⟨e.1.1,(actual_mem_vertex_support (MarkedPattern d) e.1.1).mpr
    ⟨e.1.2,(actual_mem_dart_support (MarkedPattern d) e.1).mpr ⟨e,he,Or.inl rfl⟩⟩⟩

theorem actual_disjoint_marked_tuple_injective {n q ell : ℕ}
    (S : Finset (Fin n)) (hell : 0<ell) (F : DisjointMarkedTuple S q ell) :
    Function.Injective F.val := by
  intro i j h
  by_contra hij
  obtain ⟨u,hu⟩ := actual_marked_vertex_support_nonempty hell (F.val i)
  exact Finset.disjoint_left.mp (F.property.2 i j hij) hu (by rw [←h];exact hu)

theorem actual_nonoverlap_joint_iff_vertex_disjoint {n q ell : ℕ}
    (hell : 3≤ell) (F : MarkedJoint n q ell) :
    ¬JointOverlaps F ↔ ∀i j,i≠j→
      Disjoint (VertexSupport (MarkedPattern (F i))) (VertexSupport (MarkedPattern (F j))) := by
  constructor
  · intro hn i j hij
    apply Finset.disjoint_left.mpr
    intro u hui huj
    apply hn
    refine ⟨i,j,?_,u,hui,huj⟩
    intro h
    exact hij (F.injective (actual_marked_pattern_injective n ell hell h))
  · intro hd hO
    obtain ⟨i,j,hne,u,hui,huj⟩ := hO
    have hij : i≠j := by intro h;subst j;exact hne rfl
    exact Finset.disjoint_left.mp (hd i j hij) hui huj

#print axioms actual_marked_pattern_card_positive
#print axioms actual_marked_vertex_support_nonempty
#print axioms actual_disjoint_marked_tuple_injective
#print axioms actual_nonoverlap_joint_iff_vertex_disjoint
end Reference.MD06CombinedMoments
