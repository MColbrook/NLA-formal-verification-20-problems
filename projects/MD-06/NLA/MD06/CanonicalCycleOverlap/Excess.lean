module

public import NLA.MD06.CanonicalCycleOverlap.FamilyDefinitions
public import NLA.MD06.CanonicalCycleOverlap.ThirdDart
public import NLA.MD06.BadOverlapExcess.Excess
public import NLA.MD06.BadJointMoments.JointCompatibility

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCycleOverlap
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06PairingCounts Reference.MD06BadOverlap Reference.MD06BadJointMoments
attribute [local instance] Classical.propDecidable

theorem actual_normalized_distinct_pair_order {n : ℕ} (x y : Dart n) (hne : x≠y) :
    DartLT (OrientedEdge x y).1 (OrientedEdge x y).2 := by
  unfold OrientedEdge
  split
  · assumption
  · change DartLT y x
    by_contra hrev
    apply hne
    apply Prod.ext <;> apply Fin.ext <;> unfold DartLT at * <;> omega

theorem actual_canonical_cycle_ordered {n ell : ℕ} (D : CycleData n ell) :
    ∀ e∈CanonicalCyclePattern D, DartLT e.1 e.2 := by
  intro e he
  rw [actual_canonical_cycle_pattern_image] at he
  rcases Finset.mem_image.mp he with ⟨i,hi,rfl⟩
  exact actual_normalized_distinct_pair_order _ _
    (actual_outgoing_ne_incoming D i (finRotate ell i))

theorem actual_canonical_cycle_vertex_min_two {n ell : ℕ}
    (D : CycleData n ell) (u : Fin n) (hu : u∈VertexSupport (CanonicalCyclePattern D)) :
    2≤(LocalSupport (CanonicalCyclePattern D) u).card := by
  rw [actual_canonical_cycle_vertex_support] at hu
  rcases Finset.mem_image.mp hu with ⟨i,hi,hiv⟩
  subst u
  exact le_of_eq (actual_cycle_canonical_local_card D i).symm

theorem actual_family_contains_cycle {n q : ℕ}
    (L : Fin q → ℕ) (D : ∀ i : Fin q, CycleData n (L i)) (i : Fin q) :
    CanonicalCyclePattern (D i) ⊆ FamilyUnion L D := by
  intro e he
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,he⟩

theorem actual_family_cycle_ordered {n q : ℕ}
    (L : Fin q → ℕ) (D : ∀ i : Fin q, CycleData n (L i)) :
    ∀ e∈FamilyUnion L D, DartLT e.1 e.2 := by
  intro e he
  rcases Finset.mem_biUnion.mp he with ⟨i,hi,hei⟩
  exact actual_canonical_cycle_ordered (D i) e hei

theorem actual_family_cycle_distinct_endpoints {n q : ℕ}
    (L : Fin q → ℕ) (D : ∀ i : Fin q, CycleData n (L i)) :
    ∀ e∈FamilyUnion L D, e.1≠e.2 := by
  intro e he h
  have ho := actual_family_cycle_ordered L D e he
  exact (actual_dart_lt_asymm ho) (by simpa only [h] using ho)

theorem actual_family_cycle_matching_dart_card {n q : ℕ}
    (L : Fin q → ℕ) (D : ∀ i : Fin q, CycleData n (L i))
    (p : Pairing n) (hp : Matches (FamilyUnion L D) p) :
    (DartSupport (FamilyUnion L D)).card=2*(FamilyUnion L D).card :=
  actual_dart_support_card_of_disjoint (FamilyUnion L D)
    (actual_family_cycle_distinct_endpoints L D)
    (actual_ordered_matching_constraints_disjoint (FamilyUnion L D) p
      (actual_family_cycle_ordered L D) hp)

theorem actual_family_cycle_vertex_min_two {n q : ℕ}
    (L : Fin q → ℕ) (D : ∀ i : Fin q, CycleData n (L i)) :
    ∀ u∈VertexSupport (FamilyUnion L D), 2≤(LocalSupport (FamilyUnion L D) u).card := by
  intro u hu
  rcases (actual_mem_vertex_support (FamilyUnion L D) u).mp hu with ⟨a,ha⟩
  rcases (actual_mem_dart_support (FamilyUnion L D) (u,a)).mp ha with ⟨e,he,ha⟩
  rcases Finset.mem_biUnion.mp he with ⟨i,hi,hei⟩
  have hui : u∈VertexSupport (CanonicalCyclePattern (D i)) :=
    (actual_mem_vertex_support _ u).mpr
      ⟨a,(actual_mem_dart_support _ (u,a)).mpr ⟨e,hei,ha⟩⟩
  exact le_trans (actual_canonical_cycle_vertex_min_two (D i) u hui)
    (Finset.card_le_card (actual_local_support_mono (actual_family_contains_cycle L D i) u))

theorem actual_family_cycle_edge_card_bound {n q : ℕ}
    (L : Fin q → ℕ) (D : ∀ i : Fin q, CycleData n (L i)) :
    (FamilyUnion L D).card≤∑ i : Fin q, L i := by
  have h := Finset.card_biUnion_le (s := Finset.univ)
    (t := fun i => CanonicalCyclePattern (D i))
  simpa only [FamilyUnion,actual_canonical_cycle_pattern_card] using h

theorem actual_family_cycle_overlap_excess {n q : ℕ}
    (L : Fin q → ℕ) (D : ∀ i : Fin q, CycleData n (L i))
    (p : Pairing n) (hp : Matches (FamilyUnion L D) p) (i j : Fin q)
    (hne : CanonicalCyclePattern (D i)≠CanonicalCyclePattern (D j))
    (hov : ¬Disjoint (VertexSupport (CanonicalCyclePattern (D i)))
      (VertexSupport (CanonicalCyclePattern (D j)))) :
    (VertexSupport (FamilyUnion L D)).card+1≤(FamilyUnion L D).card := by
  rcases actual_matched_cycle_overlap_third_dart (FamilyUnion L D) (D i) (D j) p hp
      (actual_family_contains_cycle L D i) (actual_family_contains_cycle L D j)
      hne hov with ⟨u,h3⟩
  have hpos : 0<(LocalSupport (FamilyUnion L D) u).card := by omega
  rcases Finset.card_pos.mp hpos with ⟨a,ha⟩
  have hu : u∈VertexSupport (FamilyUnion L D) :=
    (actual_mem_vertex_support _ u).mpr
      ⟨a,(actual_mem_local_support _ u a).mp ha⟩
  have h := actual_dart_support_card_gt_two_vertices (FamilyUnion L D)
    (actual_family_cycle_vertex_min_two L D) u hu h3
  rw [actual_family_cycle_matching_dart_card L D p hp] at h
  omega

theorem actual_family_cycle_overlap_support_bound {n q : ℕ}
    (L : Fin q → ℕ) (D : ∀ i : Fin q, CycleData n (L i))
    (p : Pairing n) (hp : Matches (FamilyUnion L D) p) (i j : Fin q)
    (hne : CanonicalCyclePattern (D i)≠CanonicalCyclePattern (D j))
    (hov : ¬Disjoint (VertexSupport (CanonicalCyclePattern (D i)))
      (VertexSupport (CanonicalCyclePattern (D j)))) :
    (VertexSupport (FamilyUnion L D)).card+1≤(FamilyUnion L D).card ∧
      (FamilyUnion L D).card≤∑ i : Fin q, L i :=
  ⟨actual_family_cycle_overlap_excess L D p hp i j hne hov,
    actual_family_cycle_edge_card_bound L D⟩

#print axioms actual_normalized_distinct_pair_order
#print axioms actual_canonical_cycle_ordered
#print axioms actual_canonical_cycle_vertex_min_two
#print axioms actual_family_contains_cycle
#print axioms actual_family_cycle_ordered
#print axioms actual_family_cycle_distinct_endpoints
#print axioms actual_family_cycle_matching_dart_card
#print axioms actual_family_cycle_vertex_min_two
#print axioms actual_family_cycle_edge_card_bound
#print axioms actual_family_cycle_overlap_excess
#print axioms actual_family_cycle_overlap_support_bound
end Reference.MD06CanonicalCycleOverlap
