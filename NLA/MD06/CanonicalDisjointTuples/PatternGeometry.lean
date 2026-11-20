module

public import NLA.MD06.CanonicalDisjointTuples.MeanDefinitions
public import NLA.MD06.CanonicalCyclePatterns.Normalization
public import NLA.MD06.JointSupportCounts.SupportProperties

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalDisjointTuples
open Reference.MD06JointSupportCounts Reference.MD06CubicConfiguration
open Reference.MD06CyclePairPatterns Reference.MD06CanonicalCyclePatterns
open Reference.MD06SupportedCanonicalCycles
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_vertex_disjoint_constraint_endpoints {n : ℕ}
    (C D : Finset (Dart n×Dart n)) (h : Disjoint (VertexSupport C) (VertexSupport D))
    (e : Dart n×Dart n) (he : e∈C) (f : Dart n×Dart n) (hf : f∈D) :
    Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hc : x∈DartSupport C :=
    (actual_mem_dart_support C x).mpr ⟨e,he,by simpa only
      [Finset.mem_insert,Finset.mem_singleton] using hx⟩
  have hd : x∈DartSupport D :=
    (actual_mem_dart_support D x).mpr ⟨f,hf,by simpa only
      [Finset.mem_insert,Finset.mem_singleton] using hy⟩
  exact Finset.disjoint_left.mp h
    ((actual_mem_vertex_support C x.1).mpr ⟨x.2,hc⟩)
    ((actual_mem_vertex_support D x.1).mpr ⟨x.2,hd⟩)

theorem actual_vertex_disjoint_constraints {n : ℕ}
    (C D : Finset (Dart n×Dart n)) (h : Disjoint (VertexSupport C) (VertexSupport D)) :
    Disjoint C D := by
  apply Finset.disjoint_left.mpr
  intro e he hd
  have hc := actual_vertex_disjoint_constraint_endpoints C D h e he e hd
  exact Finset.disjoint_left.mp hc (Finset.mem_insert_self _ _) (Finset.mem_insert_self _ _)

theorem actual_tuple_union_card {n q : ℕ} (S : Finset (Fin n)) (L : Fin q→ℕ)
    (F : CanonicalTuple S L) : (TupleUnion F).card=CycleWeight L := by
  have hd : (↑(Finset.univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint F.val := by
    intro i _ j _ hij
    exact actual_vertex_disjoint_constraints _ _ (F.property.2.2 i j hij)
  have hc (i : Fin q) : (F.val i).card=L i := by
    obtain ⟨D,hD⟩ := F.property.1 i
    rw [←hD]
    exact actual_canonical_cycle_pattern_card D
  rw [TupleUnion,Finset.card_biUnion hd]
  simp_rw [hc]
  rfl

theorem actual_tuple_union_distinct_endpoints {n q : ℕ} (S : Finset (Fin n))
    (L : Fin q→ℕ) (F : CanonicalTuple S L) :
    ∀e∈TupleUnion F,e.1≠e.2 := by
  intro e he
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
  obtain ⟨D,hD⟩ := F.property.1 i
  rw [←hD] at hi
  exact actual_normalized_constraints_distinct_endpoints (CyclePattern D)
    (actual_cycle_pattern_distinct_endpoints D) e hi

theorem actual_tuple_union_disjoint_endpoints {n q : ℕ} (S : Finset (Fin n))
    (L : Fin q→ℕ) (F : CanonicalTuple S L) :
    ∀e∈TupleUnion F,∀f∈TupleUnion F,e≠f→
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  intro e he f hf hef
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp he
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hf
  by_cases hij : i=j
  · subst j
    obtain ⟨D,hD⟩ := F.property.1 i
    rw [←hD] at hi hj
    exact actual_normalized_constraints_disjoint_endpoints (CyclePattern D)
      (actual_cycle_pattern_disjoint_endpoints D) e hi f hj hef
  · exact actual_vertex_disjoint_constraint_endpoints _ _
      (F.property.2.2 i j hij) e hi f hj

#print axioms actual_vertex_disjoint_constraint_endpoints
#print axioms actual_vertex_disjoint_constraints
#print axioms actual_tuple_union_card
#print axioms actual_tuple_union_distinct_endpoints
#print axioms actual_tuple_union_disjoint_endpoints
end Reference.MD06CanonicalDisjointTuples
