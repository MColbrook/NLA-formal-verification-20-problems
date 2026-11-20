module

public import NLA.MD06.CanonicalCycleOverlap.Propagation

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCycleOverlap
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

theorem actual_shared_matched_cycle_equal {n ell ell' : ℕ}
    (C : Finset (Dart n × Dart n)) (D : CycleData n ell) (E : CycleData n ell')
    (p : Pairing n) (hp : Matches C p)
    (hD : CanonicalCyclePattern D ⊆ C) (hE : CanonicalCyclePattern E ⊆ C)
    (h2 : ∀ u : Fin n, (LocalSupport C u).card≤2)
    (i : Fin ell) (j : Fin ell') (hv : D.1 i=E.1 j) :
    CanonicalCyclePattern D=CanonicalCyclePattern E := by
  let := i.neZero
  let := j.neZero
  have hf : ({(D.2 i).val.1,(D.2 i).val.2} : Finset (Fin 3))=
      {(E.2 j).val.1,(E.2 j).val.2} := by
    rw [←actual_canonical_cycle_local_support D i,
      actual_cycle_local_equals_common C D hD h2 i,hv,
      ←actual_cycle_local_equals_common C E hE h2 j,
      actual_canonical_cycle_local_support E j]
  have hm : (D.2 i).val.1 ∈ ({(E.2 j).val.1,(E.2 j).val.2} : Finset (Fin 3)) := by
    rw [←hf]
    exact Finset.mem_insert_self _ _
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  have hR : CanonicalCyclePattern (RotatedCycle D i) ⊆ C := by
    rw [actual_rotated_cycle_pattern]
    exact hD
  rcases hm with ha | ha
  · have hT : CanonicalCyclePattern (RotatedCycle E j) ⊆ C := by
      rw [actual_rotated_cycle_pattern]
      exact hE
    have hs : incoming (RotatedCycle D i) 0=incoming (RotatedCycle E j) 0 := by
      have hh : incoming D i=incoming E j := Prod.ext hv ha
      simpa [incoming,RotatedCycle,finCycle_apply] using hh
    simpa only [actual_rotated_cycle_pattern] using
      actual_common_cycle_pattern_equal C (RotatedCycle D i) (RotatedCycle E j)
        p hp hR hT h2 hs
  · have hT : CanonicalCyclePattern (ReflectedCycle (RotatedCycle E j)) ⊆ C := by
      rw [actual_reflected_cycle_pattern,actual_rotated_cycle_pattern]
      exact hE
    have hs : incoming (RotatedCycle D i) 0=
        incoming (ReflectedCycle (RotatedCycle E j)) 0 := by
      have hh : incoming D i=outgoing E j := Prod.ext hv ha
      simpa [incoming,outgoing,RotatedCycle,ReflectedCycle,finCycle_apply] using hh
    simpa only [actual_reflected_cycle_pattern,actual_rotated_cycle_pattern] using
      actual_common_cycle_pattern_equal C (RotatedCycle D i)
        (ReflectedCycle (RotatedCycle E j)) p hp hR hT h2 hs

theorem actual_matched_cycle_overlap_third_dart {n ell ell' : ℕ}
    (C : Finset (Dart n × Dart n)) (D : CycleData n ell) (E : CycleData n ell')
    (p : Pairing n) (hp : Matches C p)
    (hD : CanonicalCyclePattern D ⊆ C) (hE : CanonicalCyclePattern E ⊆ C)
    (hne : CanonicalCyclePattern D≠CanonicalCyclePattern E)
    (hov : ¬Disjoint (VertexSupport (CanonicalCyclePattern D))
      (VertexSupport (CanonicalCyclePattern E))) :
    ∃ u : Fin n, 3≤(LocalSupport C u).card := by
  by_contra hn
  have h2 : ∀ u : Fin n, (LocalSupport C u).card≤2 := by
    intro u
    by_contra h
    apply hn
    exact ⟨u,by omega⟩
  apply hov
  apply Finset.disjoint_left.mpr
  intro u huD huE
  rw [actual_canonical_cycle_vertex_support] at huD huE
  rcases Finset.mem_image.mp huD with ⟨i,hi,hiv⟩
  rcases Finset.mem_image.mp huE with ⟨j,hj,hjv⟩
  exact hne (actual_shared_matched_cycle_equal C D E p hp hD hE h2 i j
    (hiv.trans hjv.symm))

theorem actual_cycle_union_matches {n ell ell' : ℕ}
    (D : CycleData n ell) (E : CycleData n ell') (p : Pairing n) :
    Matches (CycleUnion D E) p ↔
      Matches (CanonicalCyclePattern D) p ∧ Matches (CanonicalCyclePattern E) p := by
  constructor
  · intro h
    exact ⟨fun e he => h e (Finset.mem_union_left _ he),
      fun e he => h e (Finset.mem_union_right _ he)⟩
  · rintro ⟨hD,hE⟩ e he
    rcases Finset.mem_union.mp he with he | he
    · exact hD e he
    · exact hE e he

theorem actual_cycle_union_third_dart {n ell ell' : ℕ}
    (D : CycleData n ell) (E : CycleData n ell') (p : Pairing n)
    (hp : Matches (CycleUnion D E) p)
    (hne : CanonicalCyclePattern D≠CanonicalCyclePattern E)
    (hov : ¬Disjoint (VertexSupport (CanonicalCyclePattern D))
      (VertexSupport (CanonicalCyclePattern E))) :
    ∃ u : Fin n, 3≤(LocalSupport (CycleUnion D E) u).card :=
  actual_matched_cycle_overlap_third_dart (CycleUnion D E) D E p hp
    Finset.subset_union_left Finset.subset_union_right hne hov

#print axioms actual_shared_matched_cycle_equal
#print axioms actual_matched_cycle_overlap_third_dart
#print axioms actual_cycle_union_matches
#print axioms actual_cycle_union_third_dart
end Reference.MD06CanonicalCycleOverlap
