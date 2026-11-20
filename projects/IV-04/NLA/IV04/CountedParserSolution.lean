module

public import NLA.IV04.PaperCountedParserComplete
public import NLA.IV04.PaperCanonicalProduct
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_natural_parser_payload_length (input : List Bool) :
    (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))).length ≤ input.length := by
  exact natural_parser_payload_length input

theorem verified_natural_parser_tail_length (input : List Bool) :
    (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))).length ≤ input.length := by
  exact natural_parser_tail_length input

theorem verified_read_natural_consumes_bit (input tail : List Bool) (value : ℕ)
    (h : IV04.Paper.readNatural input=some (value,tail)) : tail.length < input.length := by
  exact read_natural_consumes_bit input tail value h

theorem verified_fuel_read_naturals_exact (fuel count : ℕ) (input : List Bool)
    (h : input.length ≤ fuel) :
    fuelReadNaturals fuel count input=IV04.Paper.readNaturals count input := by
  exact fuel_read_naturals_exact fuel count input h

theorem verified_bounded_read_integer_weights_exact (input : List Bool) :
    boundedReadIntegerWeights input=IV04.Paper.readIntegerWeights input := by
  exact bounded_read_integer_weights_exact input

theorem verified_decrement_count_value (count : List Bool) :
    wordValue (decrementCount count)=wordValue count-1 := by
  exact decrement_count_value count

theorem verified_decrement_count_length (count : List Bool) :
    (decrementCount count).length ≤ count.length := by
  exact decrement_count_length count

theorem verified_counted_pack_cobham {n : ℕ}
    {count flag rest output : (Fin n → List Bool) → List Bool}
    (hc : Cobham count) (hf : Cobham flag) (hr : Cobham rest) (ho : Cobham output) :
    Cobham fun v => countedPack (count v) (flag v) (rest v) (output v) := by
  exact counted_pack_cobham hc hf hr ho

theorem verified_decrement_count_cobham :
    Cobham fun v : Fin 1 → List Bool => decrementCount (v 0) := by
  exact decrement_count_cobham

theorem verified_counted_step_cobham :
    Cobham fun v : Fin 1 → List Bool => countedStep (v 0) := by
  exact counted_step_cobham

theorem verified_counted_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => countedInitial (v 0) := by
  exact counted_initial_cobham

theorem verified_natural_parser_success_budget (input : List Bool)
    (h : Complexity.pairFst (encodedNaturalParser input)=[true]) :
    (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))).length+
      (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))).length+1 ≤ input.length := by
  exact natural_parser_success_budget input h

theorem verified_counted_step_pack (count rest output : List Bool) (valid : Bool) :
    countedStep (countedPack count [valid] rest output)=
      if wordValue count=0 then countedPack count [valid] rest output
      else if valid then
        if Complexity.pairFst (encodedNaturalParser rest)=[true] then
          countedPack (decrementCount count) [true]
            (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser rest)))
            (Complexity.pair (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser rest))) output)
        else countedPack count [false] rest output
      else countedPack count [valid] rest output := by
  exact counted_step_pack count rest output valid

theorem verified_counted_step_shape (count rest output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (r o : List Bool),
      countedStep (countedPack count [valid] rest output)=countedPack c [b] r o ∧
      (countedPack c [b] r o).length ≤ (countedPack count [valid] rest output).length := by
  exact counted_step_shape count rest output valid

theorem verified_counted_iterate_shape (k : ℕ) (count rest output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (r o : List Bool),
      (countedStep^[k]) (countedPack count [valid] rest output)=countedPack c [b] r o ∧
      (countedPack c [b] r o).length ≤ (countedPack count [valid] rest output).length := by
  exact counted_iterate_shape k count rest output valid

theorem verified_counted_iterate_length (k : ℕ) (count rest output : List Bool) (valid : Bool) :
    ((countedStep^[k]) (countedPack count [valid] rest output)).length ≤
      (countedPack count [valid] rest output).length := by
  exact counted_iterate_length k count rest output valid

theorem verified_counted_initial_length (input : List Bool) : (countedInitial input).length ≤ 4*input.length+8 := by
  exact counted_initial_length input

theorem verified_counted_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((countedStep^[k]) (countedInitial input)).length ≤ 4*input.length+8 := by
  exact counted_initial_iterate_length k input

theorem verified_counted_machine_state_length (input : List Bool) :
    (countedMachineState input).length ≤ 4*input.length+8 := by
  exact counted_machine_state_length input

theorem verified_counted_machine_state_cobham :
    Cobham fun v : Fin 1 → List Bool => countedMachineState (v 0) := by
  exact counted_machine_state_cobham

theorem verified_encoded_counted_natural_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedCountedNaturalParser (v 0) := by
  exact encoded_counted_natural_parser_cobham

theorem verified_encoded_counted_natural_parser_mem_fp : encodedCountedNaturalParser ∈ FP := by
  exact encoded_counted_natural_parser_mem_fp

theorem verified_payload_pair_ne_nil (payload output : List Bool) : Complexity.pair payload output ≠ [] := by
  exact payload_pair_ne_nil payload output

theorem verified_decode_payloads_code (fuel : ℕ) (payloads : List (List Bool))
    (h : (payloadListCode payloads).length ≤ fuel) :
    decodePayloads fuel (payloadListCode payloads)=payloads.map wordValue := by
  exact decode_payloads_code fuel payloads h

theorem verified_counted_state_result_pack (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    countedStateResult (countedPack count [valid] rest (payloadListCode payloads))=
      if wordValue count=0 ∧ valid=true then some ((payloads.map wordValue).reverse,rest) else none := by
  exact counted_state_result_pack count rest valid payloads

theorem verified_counted_iterate_run (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    (countedStep^[fuel]) (countedPack count [valid] rest (payloadListCode payloads))=
      countedRun fuel count valid rest payloads := by
  exact counted_iterate_run fuel count rest valid payloads

theorem verified_read_natural_of_flag_true (input : List Bool)
    (h : Complexity.pairFst (encodedNaturalParser input)=[true]) :
    IV04.Paper.readNatural input=some
      (wordValue (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))) := by
  exact read_natural_of_flag_true input h

theorem verified_read_natural_of_flag_false (input : List Bool)
    (h : Complexity.pairFst (encodedNaturalParser input)=[false]) :
    IV04.Paper.readNatural input=none := by
  exact read_natural_of_flag_false input h

theorem verified_counted_run_result (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    countedStateResult (countedRun fuel count valid rest payloads)=
      if valid then (fuelReadNaturals fuel (wordValue count) rest).map
        (fun x => ((payloads.map wordValue).reverse ++ x.1,x.2)) else none := by
  exact counted_run_result fuel count rest valid payloads

theorem verified_counted_machine_flag_boolean (input : List Bool) :
    countedFlag (countedMachineState input)=[true] ∨ countedFlag (countedMachineState input)=[false] := by
  exact counted_machine_flag_boolean input

theorem verified_counted_parser_result_eq_state (input : List Bool) :
    countedParserResult input=countedStateResult (countedMachineState input) := by
  exact counted_parser_result_eq_state input

theorem verified_counted_parser_exact (input : List Bool) :
    countedParserResult input=IV04.Paper.readIntegerWeights input := by
  exact counted_parser_exact input

theorem verified_counted_parser_actual_polytime : encodedCountedNaturalParser ∈ FP ∧
    ∀ input, countedParserResult input=IV04.Paper.readIntegerWeights input := by
  exact counted_parser_actual_polytime

theorem verified_canonical_word_multiply_value (left right : List Bool) :
    wordValue (canonicalWordMultiply left right)=wordValue left*wordValue right := by
  exact canonical_word_multiply_value left right

theorem verified_binary_product_size (left right : List Bool) :
    (wordValue left*wordValue right).size ≤ left.length+right.length := by
  exact binary_product_size left right

theorem verified_canonical_word_multiply_length (left right : List Bool) :
    (canonicalWordMultiply left right).length ≤ left.length+right.length := by
  exact canonical_word_multiply_length left right

theorem verified_polynomial_signed_multiply_linear_length (left right : List Bool) :
    (polynomialSignedMultiply left right).length ≤ left.tail.length+right.tail.length+1 := by
  exact polynomial_signed_multiply_linear_length left right

theorem verified_canonical_word_multiply_cobham :
    Cobham fun v : Fin 2 → List Bool => canonicalWordMultiply (v 0) (v 1) := by
  exact canonical_word_multiply_cobham

theorem verified_encoded_canonical_word_multiply_mem_fp : encodedCanonicalWordMultiply ∈ FP := by
  exact encoded_canonical_word_multiply_mem_fp

theorem verified_canonical_word_multiply_actual_polytime : encodedCanonicalWordMultiply ∈ FP ∧
    ∀ left right, wordValue (encodedCanonicalWordMultiply (pair left right))=wordValue left*wordValue right ∧
      (encodedCanonicalWordMultiply (pair left right)).length ≤ left.length+right.length := by
  exact canonical_word_multiply_actual_polytime

#print axioms IV04.Paper.Computational.verified_natural_parser_payload_length
#print axioms IV04.Paper.Computational.verified_natural_parser_tail_length
#print axioms IV04.Paper.Computational.verified_read_natural_consumes_bit
#print axioms IV04.Paper.Computational.verified_fuel_read_naturals_exact
#print axioms IV04.Paper.Computational.verified_bounded_read_integer_weights_exact
#print axioms IV04.Paper.Computational.verified_decrement_count_value
#print axioms IV04.Paper.Computational.verified_decrement_count_length
#print axioms IV04.Paper.Computational.verified_counted_pack_cobham
#print axioms IV04.Paper.Computational.verified_decrement_count_cobham
#print axioms IV04.Paper.Computational.verified_counted_step_cobham
#print axioms IV04.Paper.Computational.verified_counted_initial_cobham
#print axioms IV04.Paper.Computational.verified_natural_parser_success_budget
#print axioms IV04.Paper.Computational.verified_counted_step_pack
#print axioms IV04.Paper.Computational.verified_counted_step_shape
#print axioms IV04.Paper.Computational.verified_counted_iterate_shape
#print axioms IV04.Paper.Computational.verified_counted_iterate_length
#print axioms IV04.Paper.Computational.verified_counted_initial_length
#print axioms IV04.Paper.Computational.verified_counted_initial_iterate_length
#print axioms IV04.Paper.Computational.verified_counted_machine_state_length
#print axioms IV04.Paper.Computational.verified_counted_machine_state_cobham
#print axioms IV04.Paper.Computational.verified_encoded_counted_natural_parser_cobham
#print axioms IV04.Paper.Computational.verified_encoded_counted_natural_parser_mem_fp
#print axioms IV04.Paper.Computational.verified_payload_pair_ne_nil
#print axioms IV04.Paper.Computational.verified_decode_payloads_code
#print axioms IV04.Paper.Computational.verified_counted_state_result_pack
#print axioms IV04.Paper.Computational.verified_counted_iterate_run
#print axioms IV04.Paper.Computational.verified_read_natural_of_flag_true
#print axioms IV04.Paper.Computational.verified_read_natural_of_flag_false
#print axioms IV04.Paper.Computational.verified_counted_run_result
#print axioms IV04.Paper.Computational.verified_counted_machine_flag_boolean
#print axioms IV04.Paper.Computational.verified_counted_parser_result_eq_state
#print axioms IV04.Paper.Computational.verified_counted_parser_exact
#print axioms IV04.Paper.Computational.verified_counted_parser_actual_polytime
#print axioms IV04.Paper.Computational.verified_canonical_word_multiply_value
#print axioms IV04.Paper.Computational.verified_binary_product_size
#print axioms IV04.Paper.Computational.verified_canonical_word_multiply_length
#print axioms IV04.Paper.Computational.verified_polynomial_signed_multiply_linear_length
#print axioms IV04.Paper.Computational.verified_canonical_word_multiply_cobham
#print axioms IV04.Paper.Computational.verified_encoded_canonical_word_multiply_mem_fp
#print axioms IV04.Paper.Computational.verified_canonical_word_multiply_actual_polytime
end IV04.Paper.Computational
