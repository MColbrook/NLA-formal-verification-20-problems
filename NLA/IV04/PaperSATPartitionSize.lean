module

public import NLA.IV04.PaperSATPartitionCode
public import NLA.IV04.PaperSATPartitionSizeDefinitions
public import Mathlib.Data.Nat.Size
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction
open Complexity.SAT

private theorem clause_length_le_encoding (c : Clause) : c.length ≤ c.encode.length := by
  induction c with
  | nil => simp
  | cons ℓ c ih =>
    simp only [Clause.encode_cons, List.length_append, List.length_cons, List.length_nil,
      doubleBits_length, Lit.encodeRaw_length]
    omega

theorem sat_clauses_le_input_length (φ : CNF) : φ.length ≤ φ.encode.length := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    simp only [CNF.encode_cons, List.length_append, List.length_cons, List.length_nil]
    omega

theorem sat_literals_le_input_length (φ : CNF) : φ.flatten.length ≤ φ.encode.length := by
  induction φ with
  | nil => simp
  | cons c φ ih =>
    have hc := clause_length_le_encoding c
    simp only [CNF.encode_cons, List.length_append, List.length_cons, List.length_nil,
      List.flatten_cons]
    omega

theorem sat_variables_le_input_length (φ : CNF) : satVariables φ ≤ φ.encode.length+1 := by
  have h := CNF.maxVar_le_encode_length φ
  unfold satVariables
  omega

theorem sat_literal_budget_le_input_length (φ : CNF) :
    satLiteralBudget φ ≤ φ.encode.length+1 := by
  have h := sat_literals_le_input_length φ
  unfold satLiteralBudget
  omega

theorem sat_clause_target_source_bound (φ : CNF) :
    satClauseTarget φ ≤ (φ.encode.length+1)^2 := by
  have h := Nat.mul_le_mul (sat_variables_le_input_length φ) (sat_literal_budget_le_input_length φ)
  simpa only [satClauseTarget, pow_two] using h

theorem sat_digit_base_source_bound (φ : CNF) :
    satDigitBase φ ≤ 4*(φ.encode.length+1)^2+3 := by
  have h := sat_clause_target_source_bound φ
  unfold satDigitBase
  omega

theorem sat_slot_count_source_bound (φ : CNF) :
    satSlotCount φ ≤ 2*(φ.encode.length+1)+φ.encode.length*(φ.encode.length+1)^2 := by
  have hv := sat_variables_le_input_length φ
  have hM := sat_clauses_le_input_length φ
  have hK := sat_clause_target_source_bound φ
  have hm := Nat.mul_le_mul hM (Nat.le_trans (Nat.sub_le (satClauseTarget φ) 1) hK)
  unfold satSlotCount
  omega

private theorem nat_lt_two_pow_self (n : ℕ) : n < 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hp : 0 < 2^n := by positivity
    omega

theorem sat_weight_digits_carry_free (φ : CNF) (i : SATSlot φ) :
    ∀ j, satWeightDigits φ i j < satDigitBase φ := by
  intro j
  have h := Finset.single_le_sum
    (fun q _ => Nat.zero_le (satWeightDigits φ q j)) (Finset.mem_univ i)
  cases j with
  | inl v =>
    rw [sat_all_variable_digits] at h
    unfold satDigitBase
    omega
  | inr q =>
    have hh := h.trans (sat_all_clause_digits_bound φ q)
    unfold satDigitBase
    omega

private theorem sat_digit_value_binary_bound (φ : CNF) (d : SATDigit φ → ℕ)
    (hd : ∀ j, d j < satDigitBase φ) :
    satDigitValue φ d < 2^(satDigitBase φ*(satVariables φ+φ.length)) := by
  have hb : 0 < satDigitBase φ := by unfold satDigitBase; omega
  have h := positional_value_lt_power (satDigitBase φ) hb (satVariables φ+φ.length)
    (fun k => d (finSumFinEquiv.symm k)) (fun k => hd _)
  have hpow := Nat.pow_le_pow_left (Nat.le_of_lt (nat_lt_two_pow_self (satDigitBase φ)))
    (satVariables φ+φ.length)
  rw [← pow_mul] at hpow
  exact lt_of_lt_of_le h hpow

theorem sat_subset_weight_binary_bound (φ : CNF) (i : SATSlot φ) :
    satSubsetWeights φ i < 2^(satDigitBase φ*(satVariables φ+φ.length)) :=
  sat_digit_value_binary_bound φ _ (sat_weight_digits_carry_free φ i)

theorem sat_subset_target_binary_bound (φ : CNF) :
    satSubsetTarget φ < 2^(satDigitBase φ*(satVariables φ+φ.length)) :=
  sat_digit_value_binary_bound φ _ (sat_target_digits_carry_free φ)

theorem sat_subset_weight_bit_bound (φ : CNF) (i : SATSlot φ) :
    (satSubsetWeights φ i).size ≤ (4*(φ.encode.length+1)^2+3)*(2*φ.encode.length+1) := by
  have hsize := Nat.size_le.mpr (sat_subset_weight_binary_bound φ i)
  have hB := sat_digit_base_source_bound φ
  have hV := sat_variables_le_input_length φ
  have hM := sat_clauses_le_input_length φ
  have hD : satVariables φ+φ.length ≤ 2*φ.encode.length+1 := by omega
  exact hsize.trans (Nat.mul_le_mul hB hD)

private theorem padding_weight_binary_bound {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (t p : ℕ) (hw : ∀ i, w i < 2^p) (ht : t < 2^p) :
    ∀ i, subsetPartitionWeights w t i < 2^(2*Fintype.card ι+3+p) := by
  let W := ∑ i, w i
  let n := Fintype.card ι
  have hW : W ≤ n*2^p := by
    calc
      W ≤ ∑ _ : ι, 2^p := Finset.sum_le_sum (fun i _ => (hw i).le)
      _ = n*2^p := by simp [n]
  have hp : 1 ≤ 2^p := by
    have h : 0 < 2^p := by positivity
    omega
  have hmul : (2*n+3)*2^p < 2^(2*n+3+p) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_right (nat_lt_two_pow_self (2*n+3)) (by positivity)
  intro i
  apply lt_of_le_of_lt _ hmul
  cases i with
  | inl j =>
    have h := (hw j).le
    have hx : 1 ≤ 2*n+3 := by omega
    have hm := Nat.mul_le_mul_right (2^p) hx
    change w j ≤ _
    nlinarith
  | inr b =>
    cases b <;> simp only [subsetPartitionWeights]
    · change W+2*t+1 ≤ _
      nlinarith
    · change 2*W+1 ≤ _
      nlinarith

theorem sat_partition_slot_card (φ : CNF) : Fintype.card (SATSlot φ) = satSlotCount φ := by
  simpa only [Fintype.card_fin] using Fintype.card_congr (satSlotFinEquiv φ)

theorem sat_partition_weight_binary_bound (φ : CNF) (i : Fin (satSlotCount φ+2)) :
    satPartitionWeight φ i <
      2^(2*satSlotCount φ+3+satDigitBase φ*(satVariables φ+φ.length)) := by
  have h := padding_weight_binary_bound (satSubsetWeights φ) (satSubsetTarget φ)
    (satDigitBase φ*(satVariables φ+φ.length)) (sat_subset_weight_binary_bound φ)
    (sat_subset_target_binary_bound φ) ((satPartitionIndexEquiv φ).symm i)
  simpa only [satPartitionWeight, sat_partition_slot_card] using h

theorem sat_partition_weight_bit_bound (φ : CNF) (i : Fin (satSlotCount φ+2)) :
    (satPartitionWeight φ i).size ≤
      2*satSlotCount φ+3+satDigitBase φ*(satVariables φ+φ.length) :=
  Nat.size_le.mpr (sat_partition_weight_binary_bound φ i)

theorem sat_partition_input_bits_bound (φ : CNF) :
    (actualSATPartition φ).inputBits ≤
      (satSlotCount φ+2)*(2*satSlotCount φ+3+satDigitBase φ*(satVariables φ+φ.length)) := by
  change (∑ i : Fin (satSlotCount φ+2), (satPartitionWeight φ i).size) ≤ _
  calc
    _ ≤ ∑ _ : Fin (satSlotCount φ+2),
      (2*satSlotCount φ+3+satDigitBase φ*(satVariables φ+φ.length)) :=
        Finset.sum_le_sum (fun i _ => sat_partition_weight_bit_bound φ i)
    _ = _ := by simp

theorem sat_partition_code_length_bound (φ : CNF) :
    (satPartitionCode φ).length ≤
      3*(satSlotCount φ+2)+1+
        2*(satSlotCount φ+2)*(2*satSlotCount φ+3+satDigitBase φ*(satVariables φ+φ.length)) := by
  have hsize : (satSlotCount φ+2).size ≤ satSlotCount φ+2 :=
    Nat.size_le.mpr (nat_lt_two_pow_self _)
  have hbits := sat_partition_input_bits_bound φ
  rw [← actual_sat_partition_code, IV04.Paper.IntegerPartition.input_code_length]
  change 2*(satSlotCount φ+2).size+1+2*(actualSATPartition φ).inputBits+(satSlotCount φ+2) ≤ _
  nlinarith only [hsize, hbits]

theorem sat_partition_code_source_length_bound (φ : CNF) :
    (satPartitionCode φ).length ≤ satSourceCodeBound φ.encode.length := by
  have hS := sat_slot_count_source_bound φ
  have hB := sat_digit_base_source_bound φ
  have hV := sat_variables_le_input_length φ
  have hM := sat_clauses_le_input_length φ
  have hD : satVariables φ+φ.length ≤ 2*φ.encode.length+1 := by omega
  have hP := Nat.mul_le_mul hB hD
  have hA : satSlotCount φ+2 ≤ satSourceSlotBound φ.encode.length+2 := by
    unfold satSourceSlotBound
    omega
  have hE : 2*satSlotCount φ+3+satDigitBase φ*(satVariables φ+φ.length) ≤
      2*satSourceSlotBound φ.encode.length+3+satSourceDigitBitBound φ.encode.length := by
    unfold satSourceSlotBound satSourceDigitBitBound
    omega
  have hproduct := Nat.mul_le_mul hA hE
  have h := sat_partition_code_length_bound φ
  unfold satSourceCodeBound
  nlinarith only [h, hA, hproduct]

theorem binary_sat_partition_output_length_bound (bits : List Bool) :
    (binarySATPartitionReduction bits).length ≤ satSourceCodeBound bits.length := by
  cases hd : CNF.decode? bits with
  | none =>
    have hlen : (binarySATPartitionReduction bits).length = 13 := by
      have h2 : (2 : ℕ).size = 2 := by decide
      simp [binarySATPartitionReduction, hd, countedWeightCode, List.ofFn_succ,
        IV04.Paper.natural_code_length, h2]
    rw [hlen]
    unfold satSourceCodeBound satSourceSlotBound satSourceDigitBitBound
    nlinarith [Nat.zero_le (bits.length*(bits.length+1)^2),
      Nat.zero_le ((4*(bits.length+1)^2+3)*(2*bits.length+1))]
  | some φ =>
    have hbits := CNF.decode?_sound hd
    rw [binarySATPartitionReduction, hd, hbits]
    exact sat_partition_code_source_length_bound φ

theorem sat_source_code_polynomial_eval (n : ℕ) :
    satSourceCodePolynomial.eval n = satSourceCodeBound n := by
  simp [satSourceCodePolynomial, satSourceCodeBound, satSourceSlotBound, satSourceDigitBitBound]

theorem binary_sat_partition_polynomial_output :
    ∃ p : Polynomial ℕ, ∀ bits : List Bool,
      (binarySATPartitionReduction bits).length ≤ p.eval bits.length := by
  refine ⟨satSourceCodePolynomial, fun bits => ?_⟩
  rw [sat_source_code_polynomial_eval]
  exact binary_sat_partition_output_length_bound bits

#print axioms sat_slot_count_source_bound
#print axioms sat_subset_weight_binary_bound
#print axioms sat_subset_target_binary_bound
#print axioms sat_subset_weight_bit_bound
#print axioms sat_partition_weight_binary_bound
#print axioms sat_partition_input_bits_bound
#print axioms binary_sat_partition_output_length_bound
#print axioms binary_sat_partition_polynomial_output
end IV04.Paper.Computational.SATReduction
