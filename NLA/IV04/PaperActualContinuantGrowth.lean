module

public import NLA.IV04.PaperActualContinuantGrowthDefinitions
public import NLA.IV04.PaperCommonDenominator
public import NLA.IV04.PaperContinuantGrowth
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational

theorem rational_table_payload_le_length {k : ℕ} (q : Fin k → ℚ) :
    rationalPayloadBits q ≤ (rationalTableCode q).length := by
  have h : rationalPayloadBits q ≤ ((List.ofFn q).flatMap rationalCode).length := by
    simp only [List.length_flatMap,List.map_ofFn,List.sum_ofFn,
      Function.comp_apply,rational_code_length,rationalPayloadBits]
    apply Finset.sum_le_sum
    intro i _
    omega
  simpa only [rationalTableCode,List.length_append] using
    h.trans (Nat.le_add_left _ _)

theorem selected_common_denominator_fraction {n k : ℕ} (q : Fin k → ℚ)
    (selection : Fin n → Fin k) :
    commonDenominatorCoefficients (selectedIntegerCoefficients q selection)
      (rationalCommonDenominator q)=selectedRationalCoefficients q selection := by
  funext i
  by_cases hi : i < n
  · simp only [commonDenominatorCoefficients,selectedIntegerCoefficients,
      selectedRationalCoefficients,dif_pos hi]
    exact common_numerator_fraction q (selection ⟨i,hi⟩)
  · simp [commonDenominatorCoefficients,selectedIntegerCoefficients,
      selectedRationalCoefficients,hi]

theorem selected_integer_binary_bound {n k : ℕ} (q : Fin k → ℚ)
    (selection : Fin n → Fin k) (i : ℕ) :
    (selectedIntegerCoefficients q selection i).natAbs ≤ 2^(2*rationalPayloadBits q) := by
  by_cases hi : i < n
  · simp only [selectedIntegerCoefficients,dif_pos hi]
    exact common_numerator_binary_bound q (selection ⟨i,hi⟩)
  · simp [selectedIntegerCoefficients,hi]

theorem actual_rational_continuant_payload {n k : ℕ} (q : Fin k → ℚ)
    (diagonal lower upper : Fin n → Fin k) :
    let value := (rationalContinuantPair (selectedRationalCoefficients q diagonal)
      (selectedRationalCoefficients q lower) (selectedRationalCoefficients q upper) n).1
    value.num.natAbs.size ≤ n*(4*rationalPayloadBits q+1)+1 ∧
      value.den.size ≤ n*rationalPayloadBits q+1 := by
  dsimp only
  rw [rationalContinuantPair_value,
    ← selected_common_denominator_fraction q diagonal,
    ← selected_common_denominator_fraction q lower,
    ← selected_common_denominator_fraction q upper]
  have h := rational_continuant_payload_bits n (selectedIntegerCoefficients q diagonal)
    (selectedIntegerCoefficients q lower) (selectedIntegerCoefficients q upper)
    (rationalCommonDenominator q) (2*rationalPayloadBits q) (rationalPayloadBits q)
    (common_denominator_positive q) (common_denominator_binary_bound q)
    (fun i _ => selected_integer_binary_bound q diagonal i)
    (fun i _ => selected_integer_binary_bound q lower i)
    (fun i _ => selected_integer_binary_bound q upper i)
  simpa only [← Nat.mul_assoc,show 2*2=4 by decide] using h

theorem actual_rational_continuant_bits_in_code {n k : ℕ} (q : Fin k → ℚ)
    (diagonal lower upper : Fin n → Fin k) (hn : n ≤ k) :
    let value := (rationalContinuantPair (selectedRationalCoefficients q diagonal)
      (selectedRationalCoefficients q lower) (selectedRationalCoefficients q upper) n).1
    value.num.natAbs.size ≤ (rationalTableCode q).length*(4*(rationalTableCode q).length+1)+1 ∧
      value.den.size ≤ (rationalTableCode q).length^2+1 := by
  dsimp only
  have h := actual_rational_continuant_payload q diagonal lower upper
  dsimp only at h
  have hS := rational_table_payload_le_length q
  have hN := hn.trans ((coefficient_count_le_payload q).trans hS)
  have hnum := Nat.mul_le_mul hN
    (show 4*rationalPayloadBits q+1 ≤ 4*(rationalTableCode q).length+1 by omega)
  have hden := Nat.mul_le_mul hN hS
  constructor
  · omega
  · nlinarith

#print axioms actual_rational_continuant_bits_in_code
end IV04.Paper.Computational
