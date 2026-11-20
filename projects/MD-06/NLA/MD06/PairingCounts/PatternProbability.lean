module

public import NLA.MD06.PairingCounts.PatternProduct
public import NLA.MD06.CubicConfiguration.PairingMeasure

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PairingCounts
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable

theorem actual_disjoint_pattern_size_bound {n : ℕ}
    (C : Finset (Dart n × Dart n)) (hd : ∀ e ∈ C, e.1 ≠ e.2)
    (hdis : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart n)) {f.1,f.2}) :
    2*C.card ≤ 3*n := by
  have h := Finset.card_le_univ (UsedDarts C)
  rw [actual_disjoint_pattern_used_card C hd hdis] at h
  simpa [Dart,Nat.mul_comm] using h

theorem actual_disjoint_pattern_denominator_ne_zero (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k))) (hd : ∀ e ∈ C, e.1 ≠ e.2)
    (hdis : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2}) :
    PairingDenominator (Size k) C.card ≠ 0 := by
  have hp := actual_disjoint_pattern_count_product C hd hdis
  intro hz
  rw [hz,mul_zero] at hp
  exact Fintype.card_ne_zero hp.symm

theorem actual_disjoint_pattern_nonempty (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k))) (hd : ∀ e ∈ C, e.1 ≠ e.2)
    (hdis : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2}) :
    Nonempty {p : Pairing (Size k) // Matches C p} := by
  have hp := actual_disjoint_pattern_count_product C hd hdis
  have hc : PatternCount C ≠ 0 := by
    intro hz
    rw [hz,zero_mul] at hp
    exact Fintype.card_ne_zero hp.symm
  apply Fintype.card_pos_iff.mp
  change 0 < PatternCount C
  exact Nat.pos_of_ne_zero hc

theorem actual_disjoint_pattern_pairing_probability (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k))) (hd : ∀ e ∈ C, e.1 ≠ e.2)
    (hdis : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2}) :
    PairingProbability (Size k) (Matches C) =
      1 / (PairingDenominator (Size k) C.card : ℝ) := by
  unfold PairingProbability
  simp only [← Nat.card_eq_fintype_card]
  have hm : Nat.card {p : Pairing (Size k) // Matches C p} = PatternCount C := by
    unfold PatternCount
    exact Nat.card_eq_fintype_card
  rw [hm,Nat.card_eq_fintype_card]
  have ht : (Fintype.card (Pairing (Size k)) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hden : (PairingDenominator (Size k) C.card : ℝ) ≠ 0 := by
    exact_mod_cast actual_disjoint_pattern_denominator_ne_zero k C hd hdis
  apply (div_eq_div_iff ht hden).mpr
  have h : (PatternCount C : ℝ) * (PairingDenominator (Size k) C.card : ℝ) =
      Fintype.card (Pairing (Size k)) := by
    exact_mod_cast actual_disjoint_pattern_count_product C hd hdis
  simpa using h

theorem actual_uniform_pairing_disjoint_pattern_probability (k : ℕ)
    (C : Finset (Dart (Size k) × Dart (Size k))) (hd : ∀ e ∈ C, e.1 ≠ e.2)
    (hdis : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      Disjoint ({e.1,e.2} : Finset (Dart (Size k))) {f.1,f.2}) :
    ((UniformPairing k).toOuterMeasure {p | Matches C p}).toReal =
      1 / (PairingDenominator (Size k) C.card : ℝ) := by
  rw [actual_pairing_probability_uniform_real]
  exact actual_disjoint_pattern_pairing_probability k C hd hdis

#print axioms actual_disjoint_pattern_size_bound
#print axioms actual_disjoint_pattern_denominator_ne_zero
#print axioms actual_disjoint_pattern_nonempty
#print axioms actual_disjoint_pattern_pairing_probability
#print axioms actual_uniform_pairing_disjoint_pattern_probability
end Reference.MD06PairingCounts