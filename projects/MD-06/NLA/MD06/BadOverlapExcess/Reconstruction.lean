module

public import NLA.MD06.BadOverlapExcess.Metadata
public import NLA.MD06.JointSupportCounts.BadSupport

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadOverlap
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open Reference.MD06BadJointMoments Reference.MD06JointSupportCounts
open Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

theorem actual_oriented_edge_forward {n : ℕ} (x y : Dart n) (h : DartLT x y) :
    OrientedEdge x y = (x,y) := by
  simp [OrientedEdge,h]

theorem actual_oriented_edge_reverse {n : ℕ} (x y : Dart n) (h : DartLT x y) :
    OrientedEdge y x = (x,y) := by
  simp [OrientedEdge,actual_dart_lt_asymm h]

theorem actual_partner_edges_reconstruct {n : ℕ}
    (C : Finset (Dart n × Dart n)) (p : Pairing n) (u : Fin n)
    (ho : ∀ e ∈ C, DartLT e.1 e.2) (hm : Matches C p)
    (hi : ∀ e ∈ C, e.1.1 = u ∨ e.2.1 = u) :
    C = PartnerEdges p u (LocalSupport C u) := by
  have hp (e : Dart n × Dart n) (he : e ∈ C) : p.val e.2 = e.1 := by
    have h := p.property.1 e.1
    rw [hm e he] at h
    exact h
  apply Finset.Subset.antisymm
  · intro e he
    rcases hi e he with h | h
    · have hxu : (u,e.1.2) = e.1 := Prod.ext h.symm rfl
      have hl : e.1.2 ∈ LocalSupport C u :=
        (actual_mem_local_support C u e.1.2).mpr
          ((actual_mem_dart_support C (u,e.1.2)).mpr ⟨e,he,Or.inl hxu⟩)
      apply Finset.mem_image.mpr
      refine ⟨e.1.2,hl,?_⟩
      rw [hxu,hm e he,actual_oriented_edge_forward _ _ (ho e he)]
    · have hxu : (u,e.2.2) = e.2 := Prod.ext h.symm rfl
      have hl : e.2.2 ∈ LocalSupport C u :=
        (actual_mem_local_support C u e.2.2).mpr
          ((actual_mem_dart_support C (u,e.2.2)).mpr ⟨e,he,Or.inr hxu⟩)
      apply Finset.mem_image.mpr
      refine ⟨e.2.2,hl,?_⟩
      rw [hxu,hp e he,actual_oriented_edge_reverse _ _ (ho e he)]
  · intro e he
    rcases Finset.mem_image.mp he with ⟨a,ha,he⟩
    rcases (actual_mem_dart_support C (u,a)).mp
        ((actual_mem_local_support C u a).mp ha) with ⟨f,hf,hx⟩
    have hfe : OrientedEdge (u,a) (p.val (u,a)) = f := by
      rcases hx with hx | hx
      · rw [hx,hm f hf,actual_oriented_edge_forward _ _ (ho f hf)]
      · rw [hx,hp f hf,actual_oriented_edge_reverse _ _ (ho f hf)]
    exact (hfe.symm.trans he) ▸ hf

theorem actual_bad_edges_incident {n : ℕ} (z : BadDatum n) (u : Fin n)
    (hu : u ∈ VertexSupport (BadPattern z)) :
    ∀ e ∈ BadPattern z, e.1.1 = u ∨ e.2.1 = u := by
  cases z with
  | inl d =>
    simp only [BadPattern,actual_loop_vertex_support,Finset.mem_singleton] at hu
    subst u
    intro e he
    have h : e = ((d.1,d.2.val.1),(d.1,d.2.val.2)) := by
      simpa only [BadPattern,LoopPattern,Finset.mem_singleton] using he
    subst e
    exact Or.inl rfl
  | inr d =>
    cases hb : d.2.2.2 <;>
      simp only [BadPattern,DoublePattern,hb,Bool.false_eq_true,if_false,if_true,
        actual_two_edge_vertex_support,Finset.mem_insert,Finset.mem_singleton] at hu <;>
      intro e he <;>
      simp only [BadPattern,DoublePattern,hb,Bool.false_eq_true,if_false,if_true,
        Finset.mem_insert,Finset.mem_singleton] at he <;>
      rcases he with rfl | rfl <;> exact hu.imp Eq.symm Eq.symm

theorem actual_bad_pattern_reconstruct {n : ℕ} (z : BadDatum n)
    (p : Pairing n) (u : Fin n) (hm : Matches (BadPattern z) p)
    (hu : u ∈ VertexSupport (BadPattern z)) :
    BadPattern z = PartnerEdges p u (LocalSupport (BadPattern z) u) := by
  exact actual_partner_edges_reconstruct (BadPattern z) p u
    (actual_bad_pattern_ordered z) hm (actual_bad_edges_incident z u hu)

theorem actual_matched_bad_local_support_injective {n : ℕ}
    (z w : BadDatum n) (p : Pairing n) (u : Fin n)
    (hz : Matches (BadPattern z) p) (hw : Matches (BadPattern w) p)
    (huz : u ∈ VertexSupport (BadPattern z))
    (huw : u ∈ VertexSupport (BadPattern w))
    (hl : LocalSupport (BadPattern z) u = LocalSupport (BadPattern w) u) :
    z = w := by
  apply actual_bad_pattern_injective n
  rw [actual_bad_pattern_reconstruct z p u hz huz,
    actual_bad_pattern_reconstruct w p u hw huw,hl]

#print axioms actual_oriented_edge_forward
#print axioms actual_oriented_edge_reverse
#print axioms actual_partner_edges_reconstruct
#print axioms actual_bad_edges_incident
#print axioms actual_bad_pattern_reconstruct
#print axioms actual_matched_bad_local_support_injective
end Reference.MD06BadOverlap
