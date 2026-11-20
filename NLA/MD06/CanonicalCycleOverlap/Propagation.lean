module

public import NLA.MD06.CanonicalCycleOverlap.Definitions
public import NLA.MD06.CanonicalCyclePatterns.Determination

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCycleOverlap
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

theorem actual_cycle_canonical_local_card {n ell : ℕ}
    (D : CycleData n ell) (i : Fin ell) :
    (LocalSupport (CanonicalCyclePattern D) (D.1 i)).card=2 := by
  rw [actual_canonical_cycle_local_support]
  simp [(D.2 i).property]

theorem actual_cycle_local_equals_common {n ell : ℕ}
    (C : Finset (Dart n × Dart n)) (D : CycleData n ell)
    (hD : CanonicalCyclePattern D ⊆ C)
    (h2 : ∀ u : Fin n, (LocalSupport C u).card≤2) (i : Fin ell) :
    LocalSupport (CanonicalCyclePattern D) (D.1 i)=LocalSupport C (D.1 i) := by
  apply Finset.eq_of_subset_of_card_le (actual_local_support_mono hD _)
  rw [actual_cycle_canonical_local_card]
  exact h2 (D.1 i)

theorem actual_common_cycle_outgoing_of_incoming {n ell ell' : ℕ}
    (C : Finset (Dart n × Dart n)) (D : CycleData n ell) (E : CycleData n ell')
    (hD : CanonicalCyclePattern D ⊆ C) (hE : CanonicalCyclePattern E ⊆ C)
    (h2 : ∀ u : Fin n, (LocalSupport C u).card≤2)
    (i : Fin ell) (j : Fin ell') (hin : incoming D i=incoming E j) :
    outgoing D i=outgoing E j := by
  have hv : D.1 i=E.1 j := congrArg Prod.fst hin
  have ha : (D.2 i).val.1=(E.2 j).val.1 := congrArg Prod.snd hin
  have hp : ({(D.2 i).val.1,(D.2 i).val.2} : Finset (Fin 3))=
      {(E.2 j).val.1,(E.2 j).val.2} := by
    rw [←actual_canonical_cycle_local_support D i,
      actual_cycle_local_equals_common C D hD h2 i,hv,
      ←actual_cycle_local_equals_common C E hE h2 j,
      actual_canonical_cycle_local_support E j]
  have hm : (D.2 i).val.2 ∈ ({(E.2 j).val.1,(E.2 j).val.2} : Finset (Fin 3)) := by
    rw [←hp]
    simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  have ho : (D.2 i).val.2=(E.2 j).val.2 := by
    rcases hm with hm | hm
    · exact False.elim ((D.2 i).property (ha.trans hm.symm))
    · exact hm
  exact Prod.ext hv ho

theorem actual_common_matched_cycle_next {n ell ell' : ℕ}
    (C : Finset (Dart n × Dart n)) (D : CycleData n ell) (E : CycleData n ell')
    (p : Pairing n) (hp : Matches C p)
    (hD : CanonicalCyclePattern D ⊆ C) (hE : CanonicalCyclePattern E ⊆ C)
    (i : Fin ell) (j : Fin ell') (hout : outgoing D i=outgoing E j) :
    incoming D (finRotate ell i)=incoming E (finRotate ell' j) := by
  have hd : Matches (CyclePattern D) p :=
    (actual_canonical_cycle_matching D p).mp (fun e he => hp e (hD he))
  have he : Matches (CyclePattern E) p :=
    (actual_canonical_cycle_matching E p).mp (fun e he => hp e (hE he))
  have hd' : p.val (outgoing D i)=incoming D (finRotate ell i) :=
    hd (cycleEdge D i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have he' : p.val (outgoing E j)=incoming E (finRotate ell' j) :=
    he (cycleEdge E j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  exact hd'.symm.trans ((congrArg p.val hout).trans he')

theorem actual_common_cycle_incoming_walk {n ell ell' : ℕ} [NeZero ell] [NeZero ell']
    (C : Finset (Dart n × Dart n)) (D : CycleData n ell) (E : CycleData n ell')
    (p : Pairing n) (hp : Matches C p)
    (hD : CanonicalCyclePattern D ⊆ C) (hE : CanonicalCyclePattern E ⊆ C)
    (h2 : ∀ u : Fin n, (LocalSupport C u).card≤2)
    (hstart : incoming D 0=incoming E 0) :
    ∀ k : ℕ, incoming D ((finRotate ell)^[k] (0 : Fin ell))=
      incoming E ((finRotate ell')^[k] (0 : Fin ell')) := by
  intro k
  induction k with
  | zero => exact hstart
  | succ k ih =>
    simp only [Function.iterate_succ',Function.comp_apply]
    exact actual_common_matched_cycle_next C D E p hp hD hE _ _
      (actual_common_cycle_outgoing_of_incoming C D E hD hE h2 _ _ ih)

theorem actual_cycle_rotate_zero_hit {ell : ℕ} [NeZero ell] (i : Fin ell) :
    (finRotate ell)^[i.val] (0 : Fin ell)=i := by
  rw [←finCycle_eq_finRotate_iterate]
  simp [finCycle_apply]

theorem actual_common_cycle_pattern_subset {n ell ell' : ℕ} [NeZero ell] [NeZero ell']
    (C : Finset (Dart n × Dart n)) (D : CycleData n ell) (E : CycleData n ell')
    (p : Pairing n) (hp : Matches C p)
    (hD : CanonicalCyclePattern D ⊆ C) (hE : CanonicalCyclePattern E ⊆ C)
    (h2 : ∀ u : Fin n, (LocalSupport C u).card≤2)
    (hstart : incoming D 0=incoming E 0) :
    CanonicalCyclePattern D ⊆ CanonicalCyclePattern E := by
  rw [actual_canonical_cycle_pattern_image]
  intro e he
  rcases Finset.mem_image.mp he with ⟨i,hi,hie⟩
  let j : Fin ell' := (finRotate ell')^[i.val] 0
  have hin : incoming D i=incoming E j := by
    simpa only [actual_cycle_rotate_zero_hit,j] using
      actual_common_cycle_incoming_walk C D E p hp hD hE h2 hstart i.val
  have hout := actual_common_cycle_outgoing_of_incoming C D E hD hE h2 i j hin
  have hn := actual_common_matched_cycle_next C D E p hp hD hE i j hout
  rw [actual_canonical_cycle_pattern_image]
  exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,
    (congrArg₂ Reference.MD06BadOverlap.OrientedEdge hout hn).symm.trans hie⟩

theorem actual_common_cycle_pattern_equal {n ell ell' : ℕ} [NeZero ell] [NeZero ell']
    (C : Finset (Dart n × Dart n)) (D : CycleData n ell) (E : CycleData n ell')
    (p : Pairing n) (hp : Matches C p)
    (hD : CanonicalCyclePattern D ⊆ C) (hE : CanonicalCyclePattern E ⊆ C)
    (h2 : ∀ u : Fin n, (LocalSupport C u).card≤2)
    (hstart : incoming D 0=incoming E 0) :
    CanonicalCyclePattern D=CanonicalCyclePattern E :=
  Finset.Subset.antisymm
    (actual_common_cycle_pattern_subset C D E p hp hD hE h2 hstart)
    (actual_common_cycle_pattern_subset C E D p hp hE hD h2 hstart.symm)

#print axioms actual_cycle_canonical_local_card
#print axioms actual_cycle_local_equals_common
#print axioms actual_common_cycle_outgoing_of_incoming
#print axioms actual_common_matched_cycle_next
#print axioms actual_common_cycle_incoming_walk
#print axioms actual_cycle_rotate_zero_hit
#print axioms actual_common_cycle_pattern_subset
#print axioms actual_common_cycle_pattern_equal
end Reference.MD06CanonicalCycleOverlap
