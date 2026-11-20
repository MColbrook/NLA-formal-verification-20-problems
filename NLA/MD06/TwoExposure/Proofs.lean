module

public import NLA.MD06.TwoExposure.Definitions
public import NLA.MD06.AdaptiveExposure.Exposure
public import NLA.MD06.ConditionalPartner.Proofs

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06TwoExposure
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
open Reference.MD06ConditionalPartner Reference.MD06AdaptiveExposure
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_second_exposure_fiber {n : ℕ} (C : Finset (Dart n × Dart n))
    (a b : Dart n) (B : Finset (Dart n)) (next : Dart n → Dart n)
    (D : Dart n → Finset (Dart n)) :
    ConditionalPairingProbability (insert (a,b) C) (TwoExposureHit a B next D) =
      if b∈B then ConditionalPartnerProbability (insert (a,b) C) (next b) (D b) else 0 := by
  by_cases hb : b∈B
  · rw [if_pos hb,ConditionalPairingProbability,ConditionalPartnerProbability]
    congr 1
    have hc : Fintype.card {p : Pairing n // Matches (insert (a,b) C) p ∧ TwoExposureHit a B next D p} =
        Fintype.card {p : Pairing n // Matches (insert (a,b) C) p ∧ p.val (next b) ∈ D b} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (by
      intro p
      constructor
      · rintro ⟨hp,h⟩
        have hm := hp (a,b) (Finset.mem_insert_self _ _)
        change p.val a=b at hm
        exact ⟨hp,by simpa only [TwoExposureHit,hm,true_and,hb] using h⟩
      · rintro ⟨hp,h⟩
        have hm := hp (a,b) (Finset.mem_insert_self _ _)
        change p.val a=b at hm
        exact ⟨hp,by simpa only [TwoExposureHit,hm,true_and,hb] using h⟩))
    exact_mod_cast hc
  · rw [if_neg hb,ConditionalPairingProbability]
    have : IsEmpty {p : Pairing n // Matches (insert (a,b) C) p ∧ TwoExposureHit a B next D p} := by
      constructor
      intro p
      have hm := p.property.1 (a,b) (Finset.mem_insert_self _ _)
      change p.val.val a=b at hm
      exact hb (hm ▸ p.property.2.1)
    simp

theorem actual_exposure_insert_card {n : ℕ} (C : Finset (Dart n × Dart n))
    (a b : Dart n) (ha : a ∉ UsedDarts C) :
    (insert (a,b) C).card = C.card+1 := by
  apply Finset.card_insert_of_notMem
  intro h
  exact ha (actual_pattern_endpoints_used C (a,b) h).1

theorem actual_two_exposure_hit_bound (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k)))
    (hd : ∀ e ∈ C,e.1≠e.2)
    (hdis : ∀ e ∈ C,∀ f ∈ C,e≠f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2})
    (a : Dart (Size k)) (ha : a ∉ UsedDarts C)
    (B : Finset (Dart (Size k))) (next : Dart (Size k) → Dart (Size k))
    (D : Dart (Size k) → Finset (Dart (Size k))) (L : ℕ)
    (hn : ∀ b∈FreePartners C a,next b ∉ UsedDarts (insert (a,b) C))
    (hD : ∀ b∈FreePartners C a,(D b).card≤L) :
    ConditionalPairingProbability C (TwoExposureHit a B next D) ≤
      (B.card : ℝ) * ((L : ℝ)/(3*Size k-2*(C.card+1)-1 : ℕ)) /
        ((FreePartners C a).card : ℝ) := by
  rw [actual_conditional_exposure_law k C hd hdis a ha]
  have hsum :
      (∑ b∈FreePartners C a,ConditionalPairingProbability (insert (a,b) C) (TwoExposureHit a B next D)) ≤
      ∑ b∈FreePartners C a,if b∈B then (L : ℝ)/(3*Size k-2*(C.card+1)-1 : ℕ) else 0 := by
    apply Finset.sum_le_sum
    intro b hb
    rw [actual_second_exposure_fiber]
    split_ifs with hbB
    · obtain ⟨hd',hdis'⟩ := actual_insert_exposure_valid C hd hdis a b ha hb
      have ht := actual_conditional_partner_probability_le k (insert (a,b) C) hd' hdis'
        (next b) (hn b hb) (D b)
      rw [actual_exposure_insert_card C a b ha] at ht
      apply ht.trans
      exact div_le_div_of_nonneg_right (by exact_mod_cast hD b hb) (Nat.cast_nonneg _)
    · rfl
  have hsimp : (∑ b∈FreePartners C a,if b∈B then
      (L : ℝ)/(3*Size k-2*(C.card+1)-1 : ℕ) else 0) =
      ((FreePartners C a ∩ B).card : ℝ) * ((L : ℝ)/(3*Size k-2*(C.card+1)-1 : ℕ)) := by
    simp [Finset.sum_const,div_eq_mul_inv]
  rw [hsimp] at hsum
  have hf : 0≤1/((FreePartners C a).card : ℝ) := by positivity
  apply (mul_le_mul_of_nonneg_left hsum hf).trans
  rw [one_div,mul_comm,← div_eq_mul_inv]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card Finset.inter_subset_right)
    (by positivity)

#print axioms actual_second_exposure_fiber
#print axioms actual_exposure_insert_card
#print axioms actual_two_exposure_hit_bound
end Reference.MD06TwoExposure
