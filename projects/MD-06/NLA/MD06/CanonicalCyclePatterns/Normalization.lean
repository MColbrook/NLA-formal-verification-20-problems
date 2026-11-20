module

public import NLA.MD06.CanonicalCyclePatterns.Definitions
public import NLA.MD06.CyclePairPatterns.PatternProperties
public import NLA.MD06.JointSupportCounts.SupportProperties

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
open Reference.MD06CyclePairPatterns Reference.MD06BadOverlap Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_normalized_pair_endpoints {n : ℕ} (x y : Dart n) :
    ({(OrientedEdge x y).1,(OrientedEdge x y).2} : Finset (Dart n))={x,y} := by
  unfold OrientedEdge
  split <;> simp [Finset.pair_comm]

theorem actual_matching_normalized_pair {n : ℕ} (p : Pairing n) (x y : Dart n) :
    p.val (OrientedEdge x y).1=(OrientedEdge x y).2 ↔ p.val x=y := by
  unfold OrientedEdge
  split
  · rfl
  · constructor
    · intro h
      have hc := congrArg p.val h
      rw [p.property.1 y] at hc
      exact hc.symm
    · intro h
      have hc := congrArg p.val h
      rw [p.property.1 x] at hc
      exact hc.symm

theorem actual_normalized_constraints_matching {n : ℕ}
    (C : Finset (Dart n × Dart n)) (p : Pairing n) :
    Matches (CanonicalConstraints C) p ↔ Matches C p := by
  constructor
  · intro h e he
    exact (actual_matching_normalized_pair p e.1 e.2).mp
      (h (OrientedEdge e.1 e.2) (Finset.mem_image.mpr ⟨e,he,rfl⟩))
  · intro h e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact (actual_matching_normalized_pair p f.1 f.2).mpr (h f hf)

theorem actual_normalized_constraints_card {n : ℕ} (C : Finset (Dart n × Dart n))
    (hj : ∀e∈C,∀f∈C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) :
    (CanonicalConstraints C).card=C.card := by
  apply Finset.card_image_of_injOn
  intro e he f hf hn
  by_contra hef
  have hs : ({e.1,e.2} : Finset (Dart n))={f.1,f.2} :=
    (actual_normalized_pair_endpoints e.1 e.2).symm.trans
      ((congrArg (fun z : Dart n × Dart n => ({z.1,z.2} : Finset (Dart n))) hn).trans
        (actual_normalized_pair_endpoints f.1 f.2))
  exact Finset.disjoint_left.mp (hj e he f hf hef)
    (Finset.mem_insert_self _ _) (by rw [←hs];exact Finset.mem_insert_self _ _)

theorem actual_normalized_constraints_distinct_endpoints {n : ℕ}
    (C : Finset (Dart n × Dart n)) (hd : ∀e∈C,e.1 ≠ e.2) :
    ∀e∈CanonicalConstraints C,e.1 ≠ e.2 := by
  intro e he
  obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
  unfold OrientedEdge
  split
  · exact hd f hf
  · exact (hd f hf).symm

theorem actual_normalized_constraints_disjoint_endpoints {n : ℕ}
    (C : Finset (Dart n × Dart n))
    (hj : ∀e∈C,∀f∈C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) :
    ∀e∈CanonicalConstraints C,∀f∈CanonicalConstraints C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2} := by
  intro e he f hf hef
  rcases Finset.mem_image.mp he with ⟨e0,he0,heq⟩
  rcases Finset.mem_image.mp hf with ⟨f0,hf0,hfq⟩
  subst e
  subst f
  rw [actual_normalized_pair_endpoints,actual_normalized_pair_endpoints]
  exact hj e0 he0 f0 hf0
    (fun h => hef (congrArg (fun e => OrientedEdge e.1 e.2) h))

theorem actual_normalized_constraints_dart_support {n : ℕ}
    (C : Finset (Dart n × Dart n)) :
    DartSupport (CanonicalConstraints C)=DartSupport C := by
  unfold DartSupport CanonicalConstraints
  rw [Finset.image_biUnion]
  simp_rw [actual_normalized_pair_endpoints]

theorem actual_normalized_constraints_vertex_support {n : ℕ}
    (C : Finset (Dart n × Dart n)) :
    VertexSupport (CanonicalConstraints C)=VertexSupport C := by
  unfold VertexSupport
  rw [actual_normalized_constraints_dart_support]

theorem actual_canonical_cycle_pattern_card {n ell : ℕ} (D : CycleData n ell) :
    (CanonicalCyclePattern D).card=ell := by
  rw [CanonicalCyclePattern,
    actual_normalized_constraints_card _ (actual_cycle_pattern_disjoint_endpoints D),
    actual_cycle_pattern_card]

theorem actual_canonical_cycle_matching {n ell : ℕ} (D : CycleData n ell) (p : Pairing n) :
    Matches (CanonicalCyclePattern D) p ↔ Matches (CyclePattern D) p :=
  actual_normalized_constraints_matching (CyclePattern D) p

#print axioms actual_normalized_pair_endpoints
#print axioms actual_matching_normalized_pair
#print axioms actual_normalized_constraints_matching
#print axioms actual_normalized_constraints_card
#print axioms actual_normalized_constraints_distinct_endpoints
#print axioms actual_normalized_constraints_disjoint_endpoints
#print axioms actual_normalized_constraints_dart_support
#print axioms actual_normalized_constraints_vertex_support
#print axioms actual_canonical_cycle_pattern_card
#print axioms actual_canonical_cycle_matching
end Reference.MD06CanonicalCyclePatterns
