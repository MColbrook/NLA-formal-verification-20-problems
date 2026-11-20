module

public import NLA.MD06.CanonicalCyclePatterns.SymmetryProperties

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06BadOverlap Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_normalized_partner_unique {n : ℕ} (C : Finset (Dart n × Dart n))
    (hj : ∀e∈C,∀f∈C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2})
    (a b c : Dart n) (hab : OrientedEdge a b ∈ C)
    (hac : OrientedEdge a c ∈ C) (hba : b≠a) : b=c := by
  have hmab : a ∈ ({(OrientedEdge a b).1,(OrientedEdge a b).2} : Finset (Dart n)) := by
    rw [actual_normalized_pair_endpoints]
    exact Finset.mem_insert_self _ _
  have hmac : a ∈ ({(OrientedEdge a c).1,(OrientedEdge a c).2} : Finset (Dart n)) := by
    rw [actual_normalized_pair_endpoints]
    exact Finset.mem_insert_self _ _
  have he : OrientedEdge a b=OrientedEdge a c := by
    by_contra h
    exact Finset.disjoint_left.mp (hj _ hab _ hac h) hmab hmac
  have hp : ({a,b} : Finset (Dart n))={a,c} :=
    (actual_normalized_pair_endpoints a b).symm.trans
      ((congrArg (fun e : Dart n × Dart n => ({e.1,e.2} : Finset (Dart n))) he).trans
        (actual_normalized_pair_endpoints a c))
  have hb : b∈({a,c} : Finset (Dart n)) := by
    rw [←hp]
    simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hb
  exact hb.resolve_left hba

theorem actual_cycle_outgoing_of_incoming {n ell : ℕ} (D E : CycleData n ell)
    (he : CanonicalCyclePattern D=CanonicalCyclePattern E) (i : Fin ell)
    (hin : incoming D i=incoming E i) : outgoing D i=outgoing E i := by
  have hv : D.1 i=E.1 i := congrArg Prod.fst hin
  have ha : (D.2 i).val.1=(E.2 i).val.1 := congrArg Prod.snd hin
  have hp : ({(D.2 i).val.1,(D.2 i).val.2} : Finset (Fin 3))=
      {(E.2 i).val.1,(E.2 i).val.2} := by
    rw [←actual_canonical_cycle_local_support D i,he,hv,
      actual_canonical_cycle_local_support E i]
  have hm : (D.2 i).val.2 ∈ ({(E.2 i).val.1,(E.2 i).val.2} : Finset (Fin 3)) := by
    rw [←hp]
    simp
  simp only [Finset.mem_insert,Finset.mem_singleton] at hm
  have ho : (D.2 i).val.2=(E.2 i).val.2 := by
    rcases hm with hm | hm
    · exact False.elim ((D.2 i).property (ha.trans hm.symm))
    · exact hm
  exact Prod.ext hv ho

theorem actual_cycle_next_incoming {n ell : ℕ} (D E : CycleData n ell)
    (he : CanonicalCyclePattern D=CanonicalCyclePattern E) (i : Fin ell)
    (hout : outgoing D i=outgoing E i) :
    incoming D (finRotate ell i)=incoming E (finRotate ell i) := by
  have hd : OrientedEdge (outgoing D i) (incoming D (finRotate ell i)) ∈
      CanonicalCyclePattern D := by
    rw [actual_canonical_cycle_pattern_image]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hc : OrientedEdge (outgoing D i) (incoming E (finRotate ell i)) ∈
      CanonicalCyclePattern D := by
    rw [he,hout,actual_canonical_cycle_pattern_image]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  exact actual_normalized_partner_unique (CanonicalCyclePattern D)
    (actual_normalized_constraints_disjoint_endpoints (CyclePattern D)
      (actual_cycle_pattern_disjoint_endpoints D))
    _ _ _ hd hc (actual_outgoing_ne_incoming D i (finRotate ell i)).symm

theorem actual_cycle_start_determines {n ell : ℕ} [NeZero ell] (D E : CycleData n ell)
    (he : CanonicalCyclePattern D=CanonicalCyclePattern E)
    (hstart : incoming D 0=incoming E 0) : D=E := by
  have ht : ∀ k : ℕ,
      incoming D ((finRotate ell)^[k] (0 : Fin ell))=
      incoming E ((finRotate ell)^[k] (0 : Fin ell)) := by
    intro k
    induction k with
    | zero => exact hstart
    | succ k ih =>
      rw [Function.iterate_succ',Function.comp_apply]
      exact actual_cycle_next_incoming D E he _
        (actual_cycle_outgoing_of_incoming D E he _ ih)
  have hin : ∀ i : Fin ell, incoming D i=incoming E i := by
    intro i
    have hi : (finRotate ell)^[i.val] (0 : Fin ell)=i := by
      rw [←finCycle_eq_finRotate_iterate]
      simp [finCycle_apply]
    simpa only [hi] using ht i.val
  apply Prod.ext
  · apply Function.Embedding.ext
    intro i
    exact congrArg Prod.fst (hin i)
  · funext i
    apply Subtype.ext
    apply Prod.ext
    · change (D.2 i).val.1=(E.2 i).val.1
      exact congrArg (fun x : Dart n => x.2) (hin i)
    · change (D.2 i).val.2=(E.2 i).val.2
      exact congrArg (fun x : Dart n => x.2)
        (actual_cycle_outgoing_of_incoming D E he i (hin i))

#print axioms actual_normalized_partner_unique
#print axioms actual_cycle_outgoing_of_incoming
#print axioms actual_cycle_next_incoming
#print axioms actual_cycle_start_determines
end Reference.MD06CanonicalCyclePatterns
