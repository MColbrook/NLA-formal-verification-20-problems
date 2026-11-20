module

public import NLA.MD06.ConditionalPartner.Definitions
public import NLA.MD06.PairingCounts.PatternProbability

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06ConditionalPartner
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_partner_event_card {n : ℕ} (C : Finset (Dart n × Dart n))
    (a : Dart n) (B : Finset (Dart n)) :
    Fintype.card {p : Pairing n // Matches C p ∧ p.val a ∈ B} =
      ∑ b ∈ B, ConstrainedMateCount C a b := by
  let e : (Σ b : B, {p : Pairing n // Matches C p ∧ p.val a = b.val}) ≃
      {p : Pairing n // Matches C p ∧ p.val a ∈ B} :=
    { toFun := fun x => ⟨x.2.val,x.2.property.1,by rw [x.2.property.2];exact x.1.property⟩
      invFun := fun p => ⟨⟨p.val.val a,p.property.2⟩,⟨p.val,p.property.1,rfl⟩⟩
      left_inv := by rintro ⟨⟨b,hb⟩,p,hp,h⟩; change p.val a=b at h; subst b; rfl
      right_inv := by intro p; rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma] at h
  calc
    _ = ∑ b : B, ConstrainedMateCount C a b.val := h.symm
    _ = _ := Finset.sum_coe_sort B (fun b => ConstrainedMateCount C a b)

theorem actual_free_partner_card {n : ℕ} (C : Finset (Dart n × Dart n))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2})
    (a : Dart n) (ha : a ∉ UsedDarts C) :
    (FreePartners C a).card = 3*n-2*C.card-1 := by
  rw [FreePartners,actual_free_dart_card C a ha,
    actual_disjoint_pattern_used_card C hd hdis]

theorem actual_free_partners_positive (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k)))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (a : Dart (Size k)) (ha : a ∉ UsedDarts C) :
    0 < (FreePartners C a).card := by
  obtain ⟨p⟩ := actual_disjoint_pattern_nonempty k C hd hdis
  apply Finset.card_pos.mpr
  refine ⟨p.val.val a,?_⟩
  simp only [FreePartners,Finset.mem_sdiff,Finset.mem_univ,true_and,
    Finset.mem_insert,not_or]
  exact ⟨fun h => p.val.property.2 a h,
    actual_matching_partner_outside C p.val p.property a ha⟩

theorem actual_conditional_single_mate (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k)))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (a b : Dart (Size k)) (ha : a ∉ UsedDarts C) :
    (ConstrainedMateCount C a b : ℝ) / (PatternCount C : ℝ) =
      if b ∈ FreePartners C a then 1 / ((FreePartners C a).card : ℝ) else 0 := by
  have hc : (PatternCount C : ℝ) ≠ 0 := by
    have hn := actual_disjoint_pattern_nonempty k C hd hdis
    have hp : 0<PatternCount C := Fintype.card_pos_iff.mpr hn
    exact_mod_cast Nat.ne_of_gt hp
  split_ifs with hb
  · have hfree : b ∉ insert a (UsedDarts C) := (Finset.mem_sdiff.mp hb).2
    have hbu : b ∉ UsedDarts C := by
      intro h;exact hfree (Finset.mem_insert_of_mem h)
    have hab : a≠b := by intro h;subst b;exact hfree (Finset.mem_insert_self _ _)
    have hf : ((FreePartners C a).card : ℝ) ≠0 := by
      exact_mod_cast Nat.ne_of_gt (actual_free_partners_positive k C hd hdis a ha)
    apply (div_eq_div_iff hc hf).mpr
    simp only [one_mul]
    have h := actual_constrained_mate_free_multiplicity C a b ha hbu hab
    exact_mod_cast (by simpa only [FreePartners,Nat.mul_comm] using h :
      ConstrainedMateCount C a b * (FreePartners C a).card = PatternCount C)
  · have hforbidden : b ∈ insert a (UsedDarts C) := by
      by_contra h
      exact hb (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,h⟩)
    rw [actual_constrained_mate_zero_forbidden C a b ha hforbidden,Nat.cast_zero,zero_div]

theorem actual_conditional_partner_uniform (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k)))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (a : Dart (Size k)) (ha : a ∉ UsedDarts C) (B : Finset (Dart (Size k))) :
    ConditionalPartnerProbability C a B =
      ((B ∩ FreePartners C a).card : ℝ) / ((FreePartners C a).card : ℝ) := by
  rw [ConditionalPartnerProbability,actual_partner_event_card,Nat.cast_sum,Finset.sum_div]
  have hs : (∑ b ∈ B,(ConstrainedMateCount C a b : ℝ)/(PatternCount C : ℝ)) =
      ∑ b ∈ B,if b∈FreePartners C a then 1/((FreePartners C a).card : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro b hb
    exact actual_conditional_single_mate k C hd hdis a b ha
  rw [hs]
  simp [Finset.sum_const,div_eq_mul_inv]

theorem actual_conditional_partner_probability_le (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k)))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (a : Dart (Size k)) (ha : a ∉ UsedDarts C) (B : Finset (Dart (Size k))) :
    ConditionalPartnerProbability C a B ≤
      (B.card : ℝ) / (3*Size k-2*C.card-1 : ℕ) := by
  rw [actual_conditional_partner_uniform k C hd hdis a ha B,
    ← actual_free_partner_card C hd hdis a ha]
  exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card Finset.inter_subset_left)
    (Nat.cast_nonneg _)

#print axioms actual_partner_event_card
#print axioms actual_free_partner_card
#print axioms actual_free_partners_positive
#print axioms actual_conditional_single_mate
#print axioms actual_conditional_partner_uniform
#print axioms actual_conditional_partner_probability_le
end Reference.MD06ConditionalPartner
