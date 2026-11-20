module

public import NLA.MD06.PatternUnions.Definitions
public import NLA.MD06.CycleMoments.PatternLimits

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PatternUnions
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06FiniteProbability Reference.MD06CycleMoments
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_union_pattern_count_bound {I : Type*} [Fintype I] {n : ℕ}
    (C : I → Finset (Dart n × Dart n)) :
    UnionPatternCount C ≤ ∑ i : I, PatternCount (C i) := by
  let f : {p : Pairing n // ∃ i : I, Matches (C i) p} →
      (Σ i : I, {p : Pairing n // Matches (C i) p}) :=
    fun p => ⟨Classical.choose p.property,⟨p.val,Classical.choose_spec p.property⟩⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun z => z.2.val) h
  have h := Fintype.card_le_of_injective f hf
  rw [Fintype.card_sigma] at h
  simpa only [UnionPatternCount,PatternCount,← Nat.card_eq_fintype_card] using h

theorem actual_pattern_family_sum_product {I : Type*} [Fintype I] {n : ℕ}
    (e : ℕ) (C : I → Finset (Dart n × Dart n))
    (hc : ∀ i, (C i).card = e)
    (hd : ∀ i, ∀ x ∈ C i, x.1 ≠ x.2)
    (hj : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, x ≠ y →
      Disjoint ({x.1,x.2} : Finset (Dart n)) {y.1,y.2}) :
    (∑ i : I, PatternCount (C i)) * PairingDenominator n e =
      Fintype.card I * Fintype.card (Pairing n) := by
  rw [Finset.sum_mul]
  have hp (i : I) : PatternCount (C i) * PairingDenominator n e =
      Fintype.card (Pairing n) := by
    have h := actual_disjoint_pattern_count_product (C i) (hd i) (hj i)
    rw [hc i] at h
    exact h
  simp [hp]

theorem actual_uniform_pairing_pattern_union_bound {I : Type*} [Fintype I]
    (k e : ℕ) (C : I → Finset (Dart (Size k) × Dart (Size k)))
    (hc : ∀ i, (C i).card = e)
    (hd : ∀ i, ∀ x ∈ C i, x.1 ≠ x.2)
    (hj : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, x ≠ y →
      Disjoint ({x.1,x.2} : Finset (Dart (Size k))) {y.1,y.2}) :
    ((UniformPairing k).toOuterMeasure {p | ∃ i : I, Matches (C i) p}).toReal ≤
      (Fintype.card I : ℝ)/(PairingDenominator (Size k) e : ℝ) := by
  by_cases hi : Nonempty I
  · obtain ⟨i⟩ := hi
    have hd0 : (PairingDenominator (Size k) e : ℝ) > 0 := by
      have h := actual_disjoint_pattern_denominator_ne_zero k (C i) (hd i) (hj i)
      rw [hc i] at h
      exact_mod_cast Nat.pos_of_ne_zero h
    have ht : (Fintype.card (Pairing (Size k)) : ℝ) > 0 := by
      exact_mod_cast Fintype.card_pos
    rw [actual_pairing_probability_uniform_real]
    have hprob : PairingProbability (Size k) (fun p => ∃ i : I, Matches (C i) p) =
        (UnionPatternCount C : ℝ) / (Fintype.card (Pairing (Size k)) : ℝ) := by
      simp only [PairingProbability,UnionPatternCount,← Nat.card_eq_fintype_card]
    rw [hprob]
    apply (div_le_div_iff₀ ht hd0).mpr
    have h := Nat.mul_le_mul_right (PairingDenominator (Size k) e)
      (actual_union_pattern_count_bound C)
    rw [actual_pattern_family_sum_product e C hc hd hj] at h
    exact_mod_cast h
  · have : IsEmpty I := ⟨fun i => hi ⟨i⟩⟩
    simp

theorem actual_uniform_scaled_pattern_union_eventual_bound (e : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∀ (I : Type) [Fintype I]
      (C : I → Finset (Dart (Size k) × Dart (Size k))),
      (∀ i, (C i).card = e) →
      (∀ i, ∀ x ∈ C i, x.1 ≠ x.2) →
      (∀ i, ∀ x ∈ C i, ∀ y ∈ C i, x ≠ y →
        Disjoint ({x.1,x.2} : Finset (Dart (Size k))) {y.1,y.2}) →
      (Size k : ℝ)^e *
        ((UniformPairing k).toOuterMeasure {p | ∃ i : I, Matches (C i) p}).toReal ≤
          (Fintype.card I : ℝ) * (2/(3 : ℝ)^e) := by
  have hs : Tendsto Size atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    simp only [Size]
    omega
  have h := hs.eventually (actual_scaled_pattern_denominator_eventual_bound e)
  filter_upwards [h] with k hk
  intro I inst C hc hd hj
  have hb := actual_uniform_pairing_pattern_union_bound k e C hc hd hj
  have hx := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (Size k : ℝ)^e)
  have hy := mul_le_mul_of_nonneg_left hk (by positivity : 0 ≤ (Fintype.card I : ℝ))
  calc
    _ ≤ (Size k : ℝ)^e * ((Fintype.card I : ℝ)/(PairingDenominator (Size k) e : ℝ)) := hx
    _ = (Fintype.card I : ℝ) * ((Size k : ℝ)^e / (PairingDenominator (Size k) e : ℝ)) := by ring
    _ ≤ _ := hy

#print axioms actual_union_pattern_count_bound
#print axioms actual_pattern_family_sum_product
#print axioms actual_uniform_pairing_pattern_union_bound
#print axioms actual_uniform_scaled_pattern_union_eventual_bound
end Reference.MD06PatternUnions