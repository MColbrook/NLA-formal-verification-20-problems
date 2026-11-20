module

public import NLA.IV04.PaperWordListSumSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_word_list_sum_step_pair (rest total : List Bool) :
    wordListSumStep (Complexity.pair rest total)=
      if rest=[] then Complexity.pair rest total else
        Complexity.pair (Complexity.pairSnd rest) (polynomialWordAdd total (Complexity.pairFst rest)) := by
  exact word_list_sum_step_pair rest total

theorem verified_word_list_sum_step_shape (rest total : List Bool) :
    ∃ r t : List Bool, wordListSumStep (Complexity.pair rest total)=Complexity.pair r t ∧
      (Complexity.pair r t).length ≤ (Complexity.pair rest total).length+1 := by
  exact word_list_sum_step_shape rest total

theorem verified_word_list_sum_iterate_shape (k : ℕ) (rest total : List Bool) :
    ∃ r t : List Bool, (wordListSumStep^[k]) (Complexity.pair rest total)=Complexity.pair r t ∧
      (Complexity.pair r t).length ≤ (Complexity.pair rest total).length+k := by
  exact word_list_sum_iterate_shape k rest total

theorem verified_word_list_sum_iterate_length (k : ℕ) (rest total : List Bool) :
    ((wordListSumStep^[k]) (Complexity.pair rest total)).length ≤
      2*rest.length+total.length+2+k := by
  exact word_list_sum_iterate_length k rest total

theorem verified_word_list_sum_step_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListSumStep (v 0) := by
  exact word_list_sum_step_cobham

theorem verified_word_list_sum_state_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListSumState (v 0) := by
  exact word_list_sum_state_cobham

theorem verified_polynomial_word_list_sum_mem_fp : polynomialWordListSum ∈ FP := by
  exact polynomial_word_list_sum_mem_fp

theorem verified_parsed_weight_total_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialParsedWeightTotal (v 0) := by
  exact parsed_weight_total_cobham

theorem verified_parsed_weight_total_mem_fp : polynomialParsedWeightTotal ∈ FP := by
  exact parsed_weight_total_mem_fp

theorem verified_word_list_sum_iterate_nil (k : ℕ) (total : List Bool) :
    (wordListSumStep^[k]) (Complexity.pair [] total)=Complexity.pair [] total := by
  exact word_list_sum_iterate_nil k total

theorem verified_word_list_sum_iteration_value (k : ℕ) (payloads : List (List Bool)) (total : List Bool)
    (h : payloads.length ≤ k) :
    wordValue (Complexity.pairSnd ((wordListSumStep^[k])
      (Complexity.pair (payloadListCode payloads) total)))=
      wordValue total+(payloads.map wordValue).sum := by
  exact word_list_sum_iteration_value k payloads total h

theorem verified_polynomial_word_list_sum_value (payloads : List (List Bool)) :
    wordValue (polynomialWordListSum (payloadListCode payloads))=(payloads.map wordValue).sum := by
  exact polynomial_word_list_sum_value payloads

theorem verified_word_list_sum_actual_polytime : polynomialWordListSum ∈ Complexity.FP ∧
    ∀ payloads, wordValue (polynomialWordListSum (payloadListCode payloads))=(payloads.map wordValue).sum := by
  exact word_list_sum_actual_polytime

theorem verified_parsed_weight_total_value (input : List Bool) (weights : List ℕ) (tail : List Bool)
    (h : IV04.Paper.readIntegerWeights input=some (weights,tail)) :
    wordValue (polynomialParsedWeightTotal input)=weights.sum := by
  exact parsed_weight_total_value input weights tail h

theorem verified_parsed_weight_total_actual_input (P : IV04.Paper.IntegerPartition) :
    wordValue (polynomialParsedWeightTotal P.inputCode)=P.total := by
  exact parsed_weight_total_actual_input P

theorem verified_parsed_weight_total_actual_polytime : polynomialParsedWeightTotal ∈ Complexity.FP ∧
    ∀ P : IV04.Paper.IntegerPartition, wordValue (polynomialParsedWeightTotal P.inputCode)=P.total := by
  exact parsed_weight_total_actual_polytime

#print axioms IV04.Paper.Computational.verified_word_list_sum_step_pair
#print axioms IV04.Paper.Computational.verified_word_list_sum_step_shape
#print axioms IV04.Paper.Computational.verified_word_list_sum_iterate_shape
#print axioms IV04.Paper.Computational.verified_word_list_sum_iterate_length
#print axioms IV04.Paper.Computational.verified_word_list_sum_step_cobham
#print axioms IV04.Paper.Computational.verified_word_list_sum_state_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_word_list_sum_mem_fp
#print axioms IV04.Paper.Computational.verified_parsed_weight_total_cobham
#print axioms IV04.Paper.Computational.verified_parsed_weight_total_mem_fp
#print axioms IV04.Paper.Computational.verified_word_list_sum_iterate_nil
#print axioms IV04.Paper.Computational.verified_word_list_sum_iteration_value
#print axioms IV04.Paper.Computational.verified_polynomial_word_list_sum_value
#print axioms IV04.Paper.Computational.verified_word_list_sum_actual_polytime
#print axioms IV04.Paper.Computational.verified_parsed_weight_total_value
#print axioms IV04.Paper.Computational.verified_parsed_weight_total_actual_input
#print axioms IV04.Paper.Computational.verified_parsed_weight_total_actual_polytime
end IV04.Paper.Computational
