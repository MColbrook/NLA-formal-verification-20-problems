module

public import NLA.IV04.PaperSATPartitionSize
public import NLA.IV04.PaperSATNPCompleteness
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complexity Complexity.SAT
open scoped BigOperators

namespace IV04.Paper.Computational
theorem verified_actual_binary_sat_np_complete : NPComplete SAT.language := actual_binary_sat_np_complete

theorem verified_actual_np_language_reduces_to_binary_sat : ∀ (L : Set (List Bool)) (hL : L ∈ NP),
  L ≤ₚ SAT.language := actual_np_language_reduces_to_binary_sat

end IV04.Paper.Computational

namespace IV04.Paper.Computational.SATReduction
theorem verified_subset_sum_iff_signed_target : ∀ {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (t : ℕ),
  HasSubsetSum w t ↔ ∃ s, IsSigned s ∧
      signedTotal w s = 2*(t : ℤ) - ((∑ i, w i : ℕ) : ℤ) := subset_sum_iff_signed_target

theorem verified_subset_partition_iff : ∀ {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (t : ℕ),
  SignedPartition (subsetPartitionWeights w t) ↔ HasSubsetSum w t := subset_partition_iff

theorem verified_subset_partition_weights_positive : ∀ {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (t : ℕ) (hw : ∀ i, 0 < w i),
  ∀ i, 0 < subsetPartitionWeights w t i := subset_partition_weights_positive

theorem verified_paper_partition_exact_signed : ∀ (P : IV04.Paper.IntegerPartition),
  P.HasPartition ↔ SignedPartition P.weight := paper_partition_exact_signed

end IV04.Paper.Computational.SATReduction

namespace IV04.Paper.Computational.SATReduction
theorem verified_positional_value_injective : ∀ (b : ℕ) (hb : 0 < b) (n : ℕ)
    (d e : Fin n → ℕ) (hd : ∀ i, d i < b) (he : ∀ i, e i < b)
    (hv : positionalValue b d = positionalValue b e),
  d = e := positional_value_injective

theorem verified_positional_value_lt_power : ∀ (b : ℕ) (hb : 0 < b) (n : ℕ)
    (d : Fin n → ℕ) (hd : ∀ i, d i < b),
  positionalValue b d < b^n := positional_value_lt_power

end IV04.Paper.Computational.SATReduction

namespace IV04.Paper.Computational.SATReduction
theorem verified_sat_selected_digits_carry_free : ∀ (φ : CNF) (selected : SATSlot φ → Bool),
  ∀ j, satSelectedDigits φ selected j < satDigitBase φ := sat_selected_digits_carry_free

theorem verified_sat_target_digits_carry_free : ∀ (φ : CNF),
  ∀ j, satTargetDigits φ j < satDigitBase φ := sat_target_digits_carry_free

theorem verified_sat_digit_value_injective : ∀ (φ : CNF) (d e : SATDigit φ → ℕ)
    (hd : ∀ j, d j < satDigitBase φ) (he : ∀ j, e j < satDigitBase φ)
    (hv : satDigitValue φ d = satDigitValue φ e),
  d = e := sat_digit_value_injective

theorem verified_sat_selected_digit_value : ∀ (φ : CNF) (selected : SATSlot φ → Bool),
  (∑ i, if selected i then satSubsetWeights φ i else 0) =
      satDigitValue φ (satSelectedDigits φ selected) := sat_selected_digit_value

theorem verified_sat_subset_sum_iff_digit_equations : ∀ (φ : CNF),
  HasSubsetSum (satSubsetWeights φ) (satSubsetTarget φ) ↔
      ∃ selected : SATSlot φ → Bool, satSelectedDigits φ selected = satTargetDigits φ := sat_subset_sum_iff_digit_equations

theorem verified_sat_subset_weights_positive : ∀ (φ : CNF),
  ∀ i, 0 < satSubsetWeights φ i := sat_subset_weights_positive

end IV04.Paper.Computational.SATReduction

namespace IV04.Paper.Computational.SATReduction
theorem verified_sat_satisfiable_iff_digit_equations : ∀ (φ : CNF),
  φ.Satisfiable ↔ ∃ selected : SATSlot φ → Bool,
      satSelectedDigits φ selected = satTargetDigits φ := sat_satisfiable_iff_digit_equations

theorem verified_sat_satisfiable_iff_actual_subset_sum : ∀ (φ : CNF),
  φ.Satisfiable ↔ HasSubsetSum (satSubsetWeights φ) (satSubsetTarget φ) := sat_satisfiable_iff_actual_subset_sum

theorem verified_sat_satisfiable_iff_positive_partition : ∀ (φ : CNF),
  φ.Satisfiable ↔ SignedPartition
      (subsetPartitionWeights (satSubsetWeights φ) (satSubsetTarget φ)) := sat_satisfiable_iff_positive_partition

theorem verified_sat_partition_all_weights_positive : ∀ (φ : CNF),
  ∀ i, 0 < subsetPartitionWeights (satSubsetWeights φ) (satSubsetTarget φ) i := sat_partition_all_weights_positive

end IV04.Paper.Computational.SATReduction

namespace IV04.Paper.Computational.SATReduction
theorem verified_signed_partition_reindex : ∀ {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : ι → ℕ),
  SignedPartition (fun j => w (e.symm j)) ↔ SignedPartition w := signed_partition_reindex

theorem verified_paper_partition_input_code_injective : Function.Injective IV04.Paper.IntegerPartition.inputCode := paper_partition_input_code_injective

theorem verified_paper_partition_code_mem_language : ∀ (P : IV04.Paper.IntegerPartition),
  P.inputCode ∈ positivePartitionLanguage ↔ P.HasPartition := paper_partition_code_mem_language

theorem verified_actual_binary_sat_partition_reduction : ∀ (bits : List Bool),
  bits ∈ Complexity.SAT.language ↔
      binarySATPartitionReduction bits ∈ positivePartitionLanguage := actual_binary_sat_partition_reduction

end IV04.Paper.Computational.SATReduction

namespace IV04.Paper.Computational.SATReduction
theorem verified_sat_clauses_le_input_length : ∀ (φ : CNF),
  φ.length ≤ φ.encode.length := sat_clauses_le_input_length

theorem verified_sat_literals_le_input_length : ∀ (φ : CNF),
  φ.flatten.length ≤ φ.encode.length := sat_literals_le_input_length

theorem verified_sat_variables_le_input_length : ∀ (φ : CNF),
  satVariables φ ≤ φ.encode.length+1 := sat_variables_le_input_length

theorem verified_sat_literal_budget_le_input_length : ∀ (φ : CNF),
  satLiteralBudget φ ≤ φ.encode.length+1 := sat_literal_budget_le_input_length

theorem verified_sat_clause_target_source_bound : ∀ (φ : CNF),
  satClauseTarget φ ≤ (φ.encode.length+1)^2 := sat_clause_target_source_bound

theorem verified_sat_digit_base_source_bound : ∀ (φ : CNF),
  satDigitBase φ ≤ 4*(φ.encode.length+1)^2+3 := sat_digit_base_source_bound

theorem verified_sat_slot_count_source_bound : ∀ (φ : CNF),
  satSlotCount φ ≤ 2*(φ.encode.length+1)+φ.encode.length*(φ.encode.length+1)^2 := sat_slot_count_source_bound

theorem verified_sat_subset_weight_binary_bound : ∀ (φ : CNF) (i : SATSlot φ),
  satSubsetWeights φ i < 2^(satDigitBase φ*(satVariables φ+φ.length)) := sat_subset_weight_binary_bound

theorem verified_sat_subset_target_binary_bound : ∀ (φ : CNF),
  satSubsetTarget φ < 2^(satDigitBase φ*(satVariables φ+φ.length)) := sat_subset_target_binary_bound

theorem verified_sat_subset_weight_bit_bound : ∀ (φ : CNF) (i : SATSlot φ),
  (satSubsetWeights φ i).size ≤ (4*(φ.encode.length+1)^2+3)*(2*φ.encode.length+1) := sat_subset_weight_bit_bound

theorem verified_sat_partition_weight_binary_bound : ∀ (φ : CNF) (i : Fin (satSlotCount φ+2)),
  satPartitionWeight φ i <
      2^(2*satSlotCount φ+3+satDigitBase φ*(satVariables φ+φ.length)) := sat_partition_weight_binary_bound

theorem verified_sat_partition_weight_bit_bound : ∀ (φ : CNF) (i : Fin (satSlotCount φ+2)),
  (satPartitionWeight φ i).size ≤
      2*satSlotCount φ+3+satDigitBase φ*(satVariables φ+φ.length) := sat_partition_weight_bit_bound

theorem verified_sat_partition_code_source_length_bound : ∀ (φ : CNF),
  (satPartitionCode φ).length ≤ satSourceCodeBound φ.encode.length := sat_partition_code_source_length_bound

theorem verified_binary_sat_partition_output_length_bound : ∀ (bits : List Bool),
  (binarySATPartitionReduction bits).length ≤ satSourceCodeBound bits.length := binary_sat_partition_output_length_bound

theorem verified_sat_source_code_polynomial_eval : ∀ (n : ℕ),
  satSourceCodePolynomial.eval n = satSourceCodeBound n := sat_source_code_polynomial_eval

theorem verified_binary_sat_partition_polynomial_output : ∃ p : Polynomial ℕ, ∀ bits : List Bool,
      (binarySATPartitionReduction bits).length ≤ p.eval bits.length := binary_sat_partition_polynomial_output

end IV04.Paper.Computational.SATReduction
#print axioms IV04.Paper.Computational.verified_actual_binary_sat_np_complete
#print axioms IV04.Paper.Computational.verified_actual_np_language_reduces_to_binary_sat
#print axioms IV04.Paper.Computational.SATReduction.verified_subset_sum_iff_signed_target
#print axioms IV04.Paper.Computational.SATReduction.verified_subset_partition_iff
#print axioms IV04.Paper.Computational.SATReduction.verified_subset_partition_weights_positive
#print axioms IV04.Paper.Computational.SATReduction.verified_paper_partition_exact_signed
#print axioms IV04.Paper.Computational.SATReduction.verified_positional_value_injective
#print axioms IV04.Paper.Computational.SATReduction.verified_positional_value_lt_power
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_selected_digits_carry_free
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_target_digits_carry_free
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_digit_value_injective
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_selected_digit_value
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_subset_sum_iff_digit_equations
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_subset_weights_positive
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_satisfiable_iff_digit_equations
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_satisfiable_iff_actual_subset_sum
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_satisfiable_iff_positive_partition
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_partition_all_weights_positive
#print axioms IV04.Paper.Computational.SATReduction.verified_signed_partition_reindex
#print axioms IV04.Paper.Computational.SATReduction.verified_paper_partition_input_code_injective
#print axioms IV04.Paper.Computational.SATReduction.verified_paper_partition_code_mem_language
#print axioms IV04.Paper.Computational.SATReduction.verified_actual_binary_sat_partition_reduction
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_clauses_le_input_length
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_literals_le_input_length
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_variables_le_input_length
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_literal_budget_le_input_length
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_clause_target_source_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_digit_base_source_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_slot_count_source_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_subset_weight_binary_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_subset_target_binary_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_subset_weight_bit_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_partition_weight_binary_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_partition_weight_bit_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_partition_code_source_length_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_binary_sat_partition_output_length_bound
#print axioms IV04.Paper.Computational.SATReduction.verified_sat_source_code_polynomial_eval
#print axioms IV04.Paper.Computational.SATReduction.verified_binary_sat_partition_polynomial_output
end
