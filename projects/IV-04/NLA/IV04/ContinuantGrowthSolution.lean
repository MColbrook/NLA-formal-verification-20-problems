module

public import NLA.IV04.PaperActualContinuantGrowth
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem verified_common_denominator_continuant (n : ℕ) (a lower upper : ℕ → ℤ)
    (D : ℕ) (hD : 0 < D) :
    rationalContinuantValue (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D) n =
      (integerContinuantValue a lower upper n : ℚ)/(D : ℚ)^n := by
  exact common_denominator_continuant n a lower upper D hD

theorem verified_common_denominator_determinant (n : ℕ) (a lower upper : ℕ → ℤ)
    (D : ℕ) (hD : 0 < D) :
    (rationalContinuantMatrix n (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D)).det =
      (integerContinuantValue a lower upper n : ℚ)/(D : ℚ)^n := by
  exact common_denominator_determinant n a lower upper D hD

theorem verified_integer_continuant_magnitude (n : ℕ) (a lower upper : ℕ → ℤ)
    (H : ℕ) (hH : 1 ≤ H)
    (ha : ∀ i < n, (a i).natAbs ≤ H)
    (hl : ∀ i < n, (lower i).natAbs ≤ H)
    (hu : ∀ i < n, (upper i).natAbs ≤ H) :
    (integerContinuantValue a lower upper n).natAbs ≤ (2*H^2)^n := by
  exact integer_continuant_magnitude n a lower upper H hH ha hl hu

theorem verified_integer_continuant_payload_bits (n : ℕ) (a lower upper : ℕ → ℤ)
    (B : ℕ)
    (ha : ∀ i < n, (a i).natAbs ≤ 2^B)
    (hl : ∀ i < n, (lower i).natAbs ≤ 2^B)
    (hu : ∀ i < n, (upper i).natAbs ≤ 2^B) :
    (integerContinuantValue a lower upper n).natAbs.size ≤ n*(2*B+1)+1 := by
  exact integer_continuant_payload_bits n a lower upper B ha hl hu

theorem verified_rational_continuant_reduced_payload (n : ℕ) (a lower upper : ℕ → ℤ)
    (D : ℕ) (hD : 0 < D) :
    let q := rationalContinuantValue (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D) n
    q.num.natAbs ≤ (integerContinuantValue a lower upper n).natAbs ∧ q.den ≤ D^n := by
  exact rational_continuant_reduced_payload n a lower upper D hD

theorem verified_rational_continuant_payload_bits (n : ℕ) (a lower upper : ℕ → ℤ)
    (D B C : ℕ) (hD : 0 < D) (hDb : D ≤ 2^C)
    (ha : ∀ i < n, (a i).natAbs ≤ 2^B)
    (hl : ∀ i < n, (lower i).natAbs ≤ 2^B)
    (hu : ∀ i < n, (upper i).natAbs ≤ 2^B) :
    let q := rationalContinuantValue (commonDenominatorCoefficients a D)
      (commonDenominatorCoefficients lower D) (commonDenominatorCoefficients upper D) n
    q.num.natAbs.size ≤ n*(2*B+1)+1 ∧ q.den.size ≤ n*C+1 := by
  exact rational_continuant_payload_bits n a lower upper D B C hD hDb ha hl hu

theorem verified_common_denominator_positive {k : ℕ} (q : Fin k → ℚ) :
    0 < rationalCommonDenominator q := by
  exact common_denominator_positive q

theorem verified_common_denominator_divisible {k : ℕ} (q : Fin k → ℚ) (i : Fin k) :
    (q i).den ∣ rationalCommonDenominator q := by
  exact common_denominator_divisible q i

theorem verified_coefficient_size_le_payload {k : ℕ} (q : Fin k → ℚ) (i : Fin k) :
    (q i).num.natAbs.size ≤ rationalPayloadBits q ∧
      (q i).den.size ≤ rationalPayloadBits q := by
  exact coefficient_size_le_payload q i

theorem verified_coefficient_count_le_payload {k : ℕ} (q : Fin k → ℚ) :
    k ≤ rationalPayloadBits q := by
  exact coefficient_count_le_payload q

theorem verified_common_denominator_binary_bound {k : ℕ} (q : Fin k → ℚ) :
    rationalCommonDenominator q ≤ 2^rationalPayloadBits q := by
  exact common_denominator_binary_bound q

theorem verified_common_numerator_fraction {k : ℕ} (q : Fin k → ℚ) (i : Fin k) :
    (rationalCommonNumerator q i : ℚ)/(rationalCommonDenominator q : ℚ)=q i := by
  exact common_numerator_fraction q i

theorem verified_common_numerator_binary_bound {k : ℕ} (q : Fin k → ℚ) (i : Fin k) :
    (rationalCommonNumerator q i).natAbs ≤ 2^(2*rationalPayloadBits q) := by
  exact common_numerator_binary_bound q i

theorem verified_rational_table_payload_le_length {k : ℕ} (q : Fin k → ℚ) :
    rationalPayloadBits q ≤ (rationalTableCode q).length := by
  exact rational_table_payload_le_length q

theorem verified_selected_common_denominator_fraction {n k : ℕ} (q : Fin k → ℚ)
    (selection : Fin n → Fin k) :
    commonDenominatorCoefficients (selectedIntegerCoefficients q selection)
      (rationalCommonDenominator q)=selectedRationalCoefficients q selection := by
  exact selected_common_denominator_fraction q selection

theorem verified_selected_integer_binary_bound {n k : ℕ} (q : Fin k → ℚ)
    (selection : Fin n → Fin k) (i : ℕ) :
    (selectedIntegerCoefficients q selection i).natAbs ≤ 2^(2*rationalPayloadBits q) := by
  exact selected_integer_binary_bound q selection i

theorem verified_actual_rational_continuant_payload {n k : ℕ} (q : Fin k → ℚ)
    (diagonal lower upper : Fin n → Fin k) :
    let value := (rationalContinuantPair (selectedRationalCoefficients q diagonal)
      (selectedRationalCoefficients q lower) (selectedRationalCoefficients q upper) n).1
    value.num.natAbs.size ≤ n*(4*rationalPayloadBits q+1)+1 ∧
      value.den.size ≤ n*rationalPayloadBits q+1 := by
  exact actual_rational_continuant_payload q diagonal lower upper

theorem verified_actual_rational_continuant_bits_in_code {n k : ℕ} (q : Fin k → ℚ)
    (diagonal lower upper : Fin n → Fin k) (hn : n ≤ k) :
    let value := (rationalContinuantPair (selectedRationalCoefficients q diagonal)
      (selectedRationalCoefficients q lower) (selectedRationalCoefficients q upper) n).1
    value.num.natAbs.size ≤ (rationalTableCode q).length*(4*(rationalTableCode q).length+1)+1 ∧
      value.den.size ≤ (rationalTableCode q).length^2+1 := by
  exact actual_rational_continuant_bits_in_code q diagonal lower upper hn

#print axioms IV04.Paper.Computational.verified_common_denominator_continuant
#print axioms IV04.Paper.Computational.verified_common_denominator_determinant
#print axioms IV04.Paper.Computational.verified_integer_continuant_magnitude
#print axioms IV04.Paper.Computational.verified_integer_continuant_payload_bits
#print axioms IV04.Paper.Computational.verified_rational_continuant_reduced_payload
#print axioms IV04.Paper.Computational.verified_rational_continuant_payload_bits
#print axioms IV04.Paper.Computational.verified_common_denominator_positive
#print axioms IV04.Paper.Computational.verified_common_denominator_divisible
#print axioms IV04.Paper.Computational.verified_coefficient_size_le_payload
#print axioms IV04.Paper.Computational.verified_coefficient_count_le_payload
#print axioms IV04.Paper.Computational.verified_common_denominator_binary_bound
#print axioms IV04.Paper.Computational.verified_common_numerator_fraction
#print axioms IV04.Paper.Computational.verified_common_numerator_binary_bound
#print axioms IV04.Paper.Computational.verified_rational_table_payload_le_length
#print axioms IV04.Paper.Computational.verified_selected_common_denominator_fraction
#print axioms IV04.Paper.Computational.verified_selected_integer_binary_bound
#print axioms IV04.Paper.Computational.verified_actual_rational_continuant_payload
#print axioms IV04.Paper.Computational.verified_actual_rational_continuant_bits_in_code
end IV04.Paper.Computational
