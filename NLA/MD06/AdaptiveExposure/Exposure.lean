module

public import NLA.MD06.AdaptiveExposure.Definitions
public import NLA.MD06.ConditionalPartner.Proofs

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06AdaptiveExposure
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
open Reference.MD06ConditionalPartner
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_insert_exposure_valid {n : ℕ} (C : Finset (Dart n × Dart n))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2})
    (a b : Dart n) (ha : a ∉ UsedDarts C) (hb : b ∈ FreePartners C a) :
    (∀ e ∈ insert (a,b) C,e.1≠e.2) ∧
      (∀ e ∈ insert (a,b) C,∀ f ∈ insert (a,b) C,e≠f →
        Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) := by
  have hbu : b ∉ UsedDarts C := by
    intro h;exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_insert_of_mem h)
  have hab : a≠b := by
    intro h;subst b;exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_insert_self _ _)
  have hf (e : Dart n × Dart n) (he : e∈C) :
      Disjoint ({a,b} : Finset (Dart n)) {e.1,e.2} := by
    apply Finset.disjoint_left.mpr
    intro x hx hxe
    have hu : x∈UsedDarts C := Finset.mem_biUnion.mpr ⟨e,he,hxe⟩
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with h | h
    · exact ha (h ▸ hu)
    · exact hbu (h ▸ hu)
  constructor
  · intro e he;rcases Finset.mem_insert.mp he with h | h
    · subst e;exact hab
    · exact hd e h
  · intro e he f hfe hef
    rcases Finset.mem_insert.mp he with he | he
    · subst e
      rcases Finset.mem_insert.mp hfe with hfe | hfe
      · exact (hef hfe.symm).elim
      · exact hf f hfe
    · rcases Finset.mem_insert.mp hfe with hfe | hfe
      · subst f;exact (hf e he).symm
      · exact hdis e he f hfe hef

theorem actual_exposure_event_partition {n : ℕ}
    (C : Finset (Dart n × Dart n)) (a : Dart n) (ha : a ∉ UsedDarts C)
    (E : Pairing n → Prop) :
    Fintype.card {p : Pairing n // Matches C p ∧ E p} =
      ∑ b ∈ FreePartners C a,
        Fintype.card {p : Pairing n // Matches (insert (a,b) C) p ∧ E p} := by
  let e : (Σ b : FreePartners C a,
      {p : Pairing n // Matches (insert (a,b.val) C) p ∧ E p}) ≃
      {p : Pairing n // Matches C p ∧ E p} :=
    { toFun := fun x => ⟨x.2.val,
        (fun f hf => x.2.property.1 f (Finset.mem_insert_of_mem hf)),x.2.property.2⟩
      invFun := fun p => ⟨⟨p.val.val a,by
        simp only [FreePartners,Finset.mem_sdiff,Finset.mem_univ,true_and,
          Finset.mem_insert,not_or]
        exact ⟨p.val.property.2 a,
          actual_matching_partner_outside C p.val p.property.1 a ha⟩⟩,
        ⟨p.val,by
          intro f hf;rcases Finset.mem_insert.mp hf with hf | hf
          · subst f;rfl
          · exact p.property.1 f hf,p.property.2⟩⟩
      left_inv := by
        rintro ⟨⟨b,hb⟩,p,hp,hE⟩
        have h := hp (a,b) (Finset.mem_insert_self _ _)
        change p.val a=b at h
        subst b;rfl
      right_inv := by intro p;rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma] at h
  calc
    _ = ∑ b : FreePartners C a,
        Fintype.card {p : Pairing n // Matches (insert (a,b.val) C) p ∧ E p} := h.symm
    _ = _ := Finset.sum_coe_sort (FreePartners C a) (fun b : Dart n =>
      Fintype.card {p : Pairing n // Matches (insert (a,b) C) p ∧ E p})

theorem actual_conditional_exposure_law (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k)))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (a : Dart (Size k)) (ha : a ∉ UsedDarts C) (E : Pairing (Size k) → Prop) :
    ConditionalPairingProbability C E =
      (1/((FreePartners C a).card : ℝ)) *
        ∑ b ∈ FreePartners C a,ConditionalPairingProbability (insert (a,b) C) E := by
  rw [ConditionalPairingProbability,actual_exposure_event_partition C a ha E,
    Nat.cast_sum,Finset.sum_div,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  obtain ⟨hd',hdis'⟩ := actual_insert_exposure_valid C hd hdis a b ha hb
  have hp := actual_disjoint_pattern_nonempty k (insert (a,b) C) hd' hdis'
  have hci : (PatternCount (insert (a,b) C) : ℝ) ≠0 := by
    exact_mod_cast Nat.ne_of_gt (Fintype.card_pos_iff.mpr hp)
  have hfree : ((FreePartners C a).card : ℝ) ≠0 := by
    exact_mod_cast Nat.ne_of_gt (actual_free_partners_positive k C hd hdis a ha)
  have hm : ((FreePartners C a).card : ℝ) * (PatternCount (insert (a,b) C) : ℝ) =
      (PatternCount C : ℝ) := by
    rw [actual_pattern_insert_count]
    exact_mod_cast actual_constrained_mate_free_multiplicity C a b ha
      (by intro h;exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_insert_of_mem h))
      (by intro h;subst b;exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_insert_self _ _))
  unfold ConditionalPairingProbability
  rw [← hm]
  field_simp

#print axioms actual_insert_exposure_valid
#print axioms actual_exposure_event_partition
#print axioms actual_conditional_exposure_law
end Reference.MD06AdaptiveExposure
