module

public import NLA.IV04.PaperPositiveWeightParser
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_payload_product_positive (payloads : List (List Bool)) :
    0 < (payloads.map wordValue).prod ↔ ∀ w ∈ payloads, 0 < wordValue w := by
  exact payload_product_positive payloads

theorem verified_positive_word_list_value (payloads : List (List Bool)) :
    polynomialPositiveWordList (payloadListCode payloads)=[decide (∀ w ∈ payloads, 0 < wordValue w)] := by
  exact positive_word_list_value payloads

theorem verified_nonempty_positive_word_list_value (payloads : List (List Bool)) :
    polynomialNonemptyPositiveWordList (payloadListCode payloads)=
      [decide (payloads ≠ [] ∧ ∀ w ∈ payloads, 0 < wordValue w)] := by
  exact nonempty_positive_word_list_value payloads

theorem verified_positive_word_list_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPositiveWordList (v 0) := by
  exact positive_word_list_cobham

theorem verified_positive_word_list_mem_fp : polynomialPositiveWordList ∈ FP := by
  exact positive_word_list_mem_fp

theorem verified_nonempty_positive_word_list_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialNonemptyPositiveWordList (v 0) := by
  exact nonempty_positive_word_list_cobham

theorem verified_nonempty_positive_word_list_mem_fp : polynomialNonemptyPositiveWordList ∈ FP := by
  exact nonempty_positive_word_list_mem_fp

theorem verified_counted_run_payload_shape (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    ∃ c b r ps, countedRun fuel count valid rest payloads=countedPack c [b] r (payloadListCode ps) := by
  exact counted_run_payload_shape fuel count rest valid payloads

theorem verified_counted_machine_payload_shape (input : List Bool) :
    ∃ c b r ps, countedMachineState input=countedPack c [b] r (payloadListCode ps) := by
  exact counted_machine_payload_shape input

theorem verified_counted_parser_payload_shape (input : List Bool) :
    ∃ b ps rest, encodedCountedNaturalParser input=pair [b] (pair (payloadListCode ps) rest) := by
  exact counted_parser_payload_shape input

theorem verified_payload_positive_reverse (ps : List (List Bool)) :
    ((ps.map wordValue).reverse ≠ [] ∧ ∀ w ∈ (ps.map wordValue).reverse, 0 < w) ↔
      (ps ≠ [] ∧ ∀ w ∈ ps, 0 < wordValue w) := by
  exact payload_positive_reverse ps

theorem verified_positive_weight_parser_exact (input : List Bool) :
    positiveWeightParserResult input=readPositiveIntegerWeights input := by
  exact positive_weight_parser_exact input

theorem verified_positive_weight_input_value (input : List Bool) :
    polynomialPositiveWeightInput input=
      [match readPositiveIntegerWeights input with | none => false | some (_,tail) => decide (tail=[])] := by
  exact positive_weight_input_value input

theorem verified_positive_weight_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedPositiveWeightParser (v 0) := by
  exact positive_weight_parser_cobham

theorem verified_positive_weight_parser_mem_fp : encodedPositiveWeightParser ∈ FP := by
  exact positive_weight_parser_mem_fp

theorem verified_positive_weight_input_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPositiveWeightInput (v 0) := by
  exact positive_weight_input_cobham

theorem verified_positive_weight_input_mem_fp : polynomialPositiveWeightInput ∈ FP := by
  exact positive_weight_input_mem_fp

theorem verified_positive_weight_parser_actual_polytime : encodedPositiveWeightParser ∈ FP ∧
    ∀ input, positiveWeightParserResult input=readPositiveIntegerWeights input := by
  exact positive_weight_parser_actual_polytime

theorem verified_positive_weight_parser_actual_input (P : IV04.Paper.IntegerPartition) (tail : List Bool) :
    positiveWeightParserResult (P.inputCode ++ tail)=some (P.weightList,tail) := by
  exact positive_weight_parser_actual_input P tail

theorem verified_positive_weight_input_actual_input (P : IV04.Paper.IntegerPartition) :
    polynomialPositiveWeightInput P.inputCode=[true] := by
  exact positive_weight_input_actual_input P

#print axioms IV04.Paper.Computational.verified_payload_product_positive
#print axioms IV04.Paper.Computational.verified_positive_word_list_value
#print axioms IV04.Paper.Computational.verified_nonempty_positive_word_list_value
#print axioms IV04.Paper.Computational.verified_positive_word_list_cobham
#print axioms IV04.Paper.Computational.verified_positive_word_list_mem_fp
#print axioms IV04.Paper.Computational.verified_nonempty_positive_word_list_cobham
#print axioms IV04.Paper.Computational.verified_nonempty_positive_word_list_mem_fp
#print axioms IV04.Paper.Computational.verified_counted_run_payload_shape
#print axioms IV04.Paper.Computational.verified_counted_machine_payload_shape
#print axioms IV04.Paper.Computational.verified_counted_parser_payload_shape
#print axioms IV04.Paper.Computational.verified_payload_positive_reverse
#print axioms IV04.Paper.Computational.verified_positive_weight_parser_exact
#print axioms IV04.Paper.Computational.verified_positive_weight_input_value
#print axioms IV04.Paper.Computational.verified_positive_weight_parser_cobham
#print axioms IV04.Paper.Computational.verified_positive_weight_parser_mem_fp
#print axioms IV04.Paper.Computational.verified_positive_weight_input_cobham
#print axioms IV04.Paper.Computational.verified_positive_weight_input_mem_fp
#print axioms IV04.Paper.Computational.verified_positive_weight_parser_actual_polytime
#print axioms IV04.Paper.Computational.verified_positive_weight_parser_actual_input
#print axioms IV04.Paper.Computational.verified_positive_weight_input_actual_input
end IV04.Paper.Computational
