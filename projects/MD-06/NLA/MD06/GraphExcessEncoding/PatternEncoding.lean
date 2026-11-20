module

public import NLA.MD06.GraphExcessEncoding.Definitions
public import NLA.MD06.BadJointMoments.JointCompatibility
public import NLA.MD06.JointSupportCounts.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06GraphExcessEncoding
open Reference.MD06CubicConfiguration Reference.MD06BoundedExcess
open Reference.MD06PairingCounts Reference.MD06JointSupportCounts
open Reference.MD06BadJointMoments
attribute [local instance] Classical.propDecidable

theorem actual_edge_darts_second_vertex {n : ℕ} {p : SimpleConfiguration n}
    {S : Finset (Fin n)} (e : GraphEdge p S) :
    (EdgeDarts e).2.1=e.val.2.val := by
  exact Classical.choose_spec e.property.2

theorem actual_edge_darts_injective {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) :
    Function.Injective (EdgeDarts (p:=p) (S:=S)) := by
  intro e f h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun x : Dart n × Dart n => x.1.1) h
  · apply Subtype.ext
    simpa only [actual_edge_darts_second_vertex] using
      congrArg (fun x : Dart n × Dart n => x.2.1) h

theorem actual_graph_edge_card {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) :
    Fintype.card (GraphEdge p S)=
      ((configurationGraph p).induce (S : Set (Fin n))).edgeFinset.card := by
  let H := (configurationGraph p).induce (S : Set (Fin n))
  let toEdge : GraphEdge p S → H.edgeSet := fun e =>
    ⟨s(e.val.1,e.val.2),H.mem_edgeSet.mpr e.property.2⟩
  have hi : Function.Injective toEdge := by
    intro e f h
    apply Subtype.ext
    have he : (Sym2.sortEquiv (s(e.val.1,e.val.2))).val=e.val := by
      simp [Sym2.sortEquiv,le_of_lt e.property.1]
    have hf : (Sym2.sortEquiv (s(f.val.1,f.val.2))).val=f.val := by
      simp [Sym2.sortEquiv,le_of_lt f.property.1]
    have hh := congrArg (fun z : H.edgeSet => (Sym2.sortEquiv z.val).val) h
    change (Sym2.sortEquiv s(e.val.1,e.val.2)).val=
      (Sym2.sortEquiv s(f.val.1,f.val.2)).val at hh
    exact he.symm.trans (hh.trans hf)
  have hs : Function.Surjective toEdge := by
    intro e
    let uv := (Sym2.sortEquiv e.val).val
    have heq : s(uv.1,uv.2)=e.val := (Sym2.sortEquiv).symm_apply_apply e.val
    have ha : H.Adj uv.1 uv.2 := H.mem_edgeSet.mp (by rw [heq];exact e.property)
    have hlt : uv.1<uv.2 := lt_of_le_of_ne (Sym2.sortEquiv e.val).property
      (H.ne_of_adj ha)
    refine ⟨⟨uv,⟨hlt,ha⟩⟩,?_⟩
    exact Subtype.ext heq
  rw [← H.card_edgeSet]
  exact Fintype.card_congr (Equiv.ofBijective toEdge ⟨hi,hs⟩)

theorem actual_induced_pattern_card {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) :
    (InducedPattern p S).card=
      ((configurationGraph p).induce (S : Set (Fin n))).edgeFinset.card := by
  unfold InducedPattern
  rw [Finset.card_image_of_injective _ (actual_edge_darts_injective p S)]
  simpa only [Finset.card_univ] using actual_graph_edge_card p S

theorem actual_induced_pattern_matches {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) : Matches (InducedPattern p S) p.val := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨e,he,rfl⟩
  rfl

theorem actual_induced_pattern_ordered {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) :
    ∀x∈InducedPattern p S,DartLT x.1 x.2 := by
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨e,he,rfl⟩
  apply Or.inl
  rw [actual_edge_darts_second_vertex]
  exact e.property.1

theorem actual_induced_pattern_distinct {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) :
    ∀x∈InducedPattern p S,x.1≠x.2 := by
  intro x hx h
  have ho := actual_induced_pattern_ordered p S x hx
  exact (actual_dart_lt_asymm ho) (by simpa only [h] using ho)

theorem actual_induced_pattern_disjoint {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) :
    ∀x∈InducedPattern p S,∀y∈InducedPattern p S,x≠y→
      Disjoint ({x.1,x.2} : Finset (Dart n)) {y.1,y.2} :=
  actual_ordered_matching_constraints_disjoint _ p.val
    (actual_induced_pattern_ordered p S) (actual_induced_pattern_matches p S)

theorem actual_induced_pattern_support_subset {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) : VertexSupport (InducedPattern p S) ⊆ S := by
  intro u hu
  rcases Finset.mem_image.mp hu with ⟨x,hx,rfl⟩
  rcases Finset.mem_biUnion.mp hx with ⟨e,he,hxe⟩
  rcases Finset.mem_image.mp he with ⟨g,hg,rfl⟩
  simp only [Finset.mem_insert,Finset.mem_singleton] at hxe
  rcases hxe with rfl | rfl
  · exact g.val.1.property
  · rw [actual_edge_darts_second_vertex]
    exact g.val.2.property

theorem actual_induced_pattern_edge_bound {n : ℕ} (p : SimpleConfiguration n)
    (S : Finset (Fin n)) : (InducedPattern p S).card≤3*S.card := by
  let f : GraphEdge p S → S × Fin 3 := fun e =>
    (e.val.1,(EdgeDarts e).1.2)
  have hi : Function.Injective f := by
    intro e g h
    apply actual_edge_darts_injective p S
    have hx : (EdgeDarts e).1=(EdgeDarts g).1 := by
      apply Prod.ext
      · exact congrArg (fun z : S × Fin 3 => z.1.val) h
      · exact congrArg (fun z : S × Fin 3 => z.2) h
    exact Prod.ext hx (congrArg p.val.val hx)
  have hc := Fintype.card_le_of_injective f hi
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_coe] at hc
  rw [actual_graph_edge_card p S,← actual_induced_pattern_card p S] at hc
  simpa only [Nat.mul_comm] using hc

#print axioms actual_edge_darts_second_vertex
#print axioms actual_edge_darts_injective
#print axioms actual_graph_edge_card
#print axioms actual_induced_pattern_card
#print axioms actual_induced_pattern_matches
#print axioms actual_induced_pattern_ordered
#print axioms actual_induced_pattern_distinct
#print axioms actual_induced_pattern_disjoint
#print axioms actual_induced_pattern_support_subset
#print axioms actual_induced_pattern_edge_bound
end Reference.MD06GraphExcessEncoding
