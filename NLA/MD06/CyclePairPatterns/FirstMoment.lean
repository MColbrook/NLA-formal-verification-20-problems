module

public import NLA.MD06.CyclePairPatterns.CountDefinitions
public import NLA.MD06.CyclePairPatterns.PatternProperties

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CyclePairPatterns
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
open scoped BigOperators

theorem actual_local_frame_card : Fintype.card LocalFrame = 6 := by decide

attribute [local instance] Classical.propDecidable

theorem actual_cycle_assignment_card (ell : ℕ) :
    Fintype.card (CycleAssignment ell) = 6^ell := by
  have hc : Fintype.card LocalFrame = 6 := by
    simpa only [← Nat.card_eq_fintype_card] using actual_local_frame_card
  rw [Fintype.card_pi]
  simp [hc]

theorem actual_cycle_data_card (n ell : ℕ) :
    Fintype.card (CycleData n ell) = n.descFactorial ell * 6^ell := by
  rw [Fintype.card_prod,actual_cycle_assignment_card,Fintype.card_embedding_eq]
  simp

theorem actual_oriented_cycle_sum {n ell : ℕ} :
    (∑ p : Pairing n, RawCycleCount n ell p) =
      ∑ D : CycleData n ell, PatternCount (CyclePattern D) := by
  let e : (Σ p : Pairing n, {D : CycleData n ell // Matches (CyclePattern D) p}) ≃
      (Σ D : CycleData n ell, {p : Pairing n // Matches (CyclePattern D) p}) :=
    { toFun := fun x => ⟨x.2.val,⟨x.1,x.2.property⟩⟩
      invFun := fun x => ⟨x.2.val,⟨x.1,x.2.property⟩⟩
      left_inv := by rintro ⟨p,D,h⟩; rfl
      right_inv := by rintro ⟨D,p,h⟩; rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma,Fintype.card_sigma] at h
  simpa only [RawCycleCount,PatternCount,← Nat.card_eq_fintype_card] using h

theorem actual_oriented_cycle_sum_product {n ell : ℕ} :
    (∑ p : Pairing n, RawCycleCount n ell p) * PairingDenominator n ell =
      Fintype.card (CycleData n ell) * Fintype.card (Pairing n) := by
  rw [actual_oriented_cycle_sum,Finset.sum_mul]
  have hp (D : CycleData n ell) :
      PatternCount (CyclePattern D) * PairingDenominator n ell =
        Fintype.card (Pairing n) := by
    have h := actual_disjoint_pattern_count_product (CyclePattern D)
      (actual_cycle_pattern_distinct_endpoints D) (actual_cycle_pattern_disjoint_endpoints D)
    rw [actual_cycle_pattern_card D] at h
    exact h
  simp [hp]

theorem actual_mean_oriented_cycles (k ell : ℕ) :
    MeanOrientedCycles k ell =
      (Fintype.card (CycleData (Size k) ell) : ℝ) /
        (PairingDenominator (Size k) ell : ℝ) := by
  by_cases hD : Nonempty (CycleData (Size k) ell)
  · obtain ⟨D⟩ := hD
    have ht : (Fintype.card (Pairing (Size k)) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hd : (PairingDenominator (Size k) ell : ℝ) ≠ 0 := by
      have hn := actual_disjoint_pattern_denominator_ne_zero k (CyclePattern D)
        (actual_cycle_pattern_distinct_endpoints D) (actual_cycle_pattern_disjoint_endpoints D)
      rw [actual_cycle_pattern_card D] at hn
      exact_mod_cast hn
    unfold MeanOrientedCycles
    rw [← Nat.cast_sum]
    apply (div_eq_div_iff ht hd).mpr
    exact_mod_cast (actual_oriented_cycle_sum_product (n := Size k) (ell := ell))
  · have : IsEmpty (CycleData (Size k) ell) := ⟨fun D => hD ⟨D⟩⟩
    simp [MeanOrientedCycles,RawCycleCount]

theorem actual_mean_oriented_cycles_formula (k ell : ℕ) :
    MeanOrientedCycles k ell =
      ((Size k).descFactorial ell : ℝ) * (6 : ℝ)^ell /
        (PairingDenominator (Size k) ell : ℝ) := by
  rw [actual_mean_oriented_cycles,actual_cycle_data_card]
  simp

#print axioms actual_local_frame_card
#print axioms actual_cycle_assignment_card
#print axioms actual_cycle_data_card
#print axioms actual_oriented_cycle_sum
#print axioms actual_oriented_cycle_sum_product
#print axioms actual_mean_oriented_cycles
#print axioms actual_mean_oriented_cycles_formula
end Reference.MD06CyclePairPatterns