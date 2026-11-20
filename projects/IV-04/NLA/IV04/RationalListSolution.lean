module

public import NLA.IV04.PaperRationalListParserComplete
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_natural_parser_payload_tail_budget (input : List Bool) :
    (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))).length+
      (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))).length ≤ input.length := by
  exact natural_parser_payload_tail_budget input

theorem verified_rational_parser_flag_boolean (input : List Bool) :
    Complexity.pairFst (encodedRationalParser input)=[true] ∨
      Complexity.pairFst (encodedRationalParser input)=[false] := by
  exact rational_parser_flag_boolean input

theorem verified_rational_parser_tail_length (input : List Bool) :
    (Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input))).length ≤ input.length := by
  exact rational_parser_tail_length input

theorem verified_rational_parser_raw_payload_budget (input : List Bool) :
    (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))).length+
      (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input))).length ≤ input.length := by
  exact rational_parser_raw_payload_budget input

theorem verified_rational_parser_fraction_length (input : List Bool) :
    (rationalParserFraction input).length ≤ 2*input.length+5 := by
  exact rational_parser_fraction_length input

theorem verified_rational_parser_success_budget (input : List Bool)
    (h : Complexity.pairFst (encodedRationalParser input)=[true]) :
    (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))).length+
      (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input))).length+
      (Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input))).length+3 ≤ input.length := by
  exact rational_parser_success_budget input h

theorem verified_read_rational_consumes_bits (input : List Bool) (q : ℚ) (tail : List Bool)
    (h : IV04.Paper.readRational input=some (q,tail)) : tail.length+3 ≤ input.length := by
  exact read_rational_consumes_bits input q tail h

theorem verified_fuel_read_rationals_exact (fuel count : ℕ) (input : List Bool)
    (h : input.length ≤ fuel) : fuelReadRationals fuel count input=readRationals count input := by
  exact fuel_read_rationals_exact fuel count input h

theorem verified_rational_list_step_pack (count rest output : List Bool) (valid : Bool) :
    rationalListStep (countedPack count [valid] rest output)=
      if wordValue count=0 then countedPack count [valid] rest output
      else if valid then
        if Complexity.pairFst (encodedRationalParser rest)=[true] then
          countedPack (decrementCount count) [true]
            (Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser rest)))
            (Complexity.pair (Complexity.pairFst (Complexity.pairSnd (encodedRationalParser rest))) output)
        else countedPack count [false] rest output
      else countedPack count [valid] rest output := by
  exact rational_list_step_pack count rest output valid

theorem verified_rational_list_step_shape (count rest output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (r o : List Bool),
      rationalListStep (countedPack count [valid] rest output)=countedPack c [b] r o ∧
      c.length ≤ count.length ∧ r.length ≤ rest.length ∧
      o.length ≤ output.length+4*rest.length+12 := by
  exact rational_list_step_shape count rest output valid

theorem verified_rational_list_iterate_shape (k : ℕ) (count rest output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (r o : List Bool),
      (rationalListStep^[k]) (countedPack count [valid] rest output)=countedPack c [b] r o ∧
      c.length ≤ count.length ∧ r.length ≤ rest.length ∧
      o.length ≤ output.length+k*(4*rest.length+12) := by
  exact rational_list_iterate_shape k count rest output valid

theorem verified_rational_list_iterate_length (k : ℕ) (count rest output : List Bool) (valid : Bool) :
    ((rationalListStep^[k]) (countedPack count [valid] rest output)).length ≤
      2*count.length+2*rest.length+output.length+8+k*(4*rest.length+12) := by
  exact rational_list_iterate_length k count rest output valid

theorem verified_rational_list_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((rationalListStep^[k]) (rationalListInitial input)).length ≤
      2*input.length+8+k*(4*input.length+12) := by
  exact rational_list_initial_iterate_length k input

theorem verified_rational_list_state_length (input : List Bool) :
    (rationalListState input).length ≤
      2*input.length+8+input.length*(4*input.length+12) := by
  exact rational_list_state_length input

theorem verified_rational_list_step_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalListStep (v 0) := by
  exact rational_list_step_cobham

theorem verified_rational_list_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalListInitial (v 0) := by
  exact rational_list_initial_cobham

theorem verified_rational_list_state_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalListState (v 0) := by
  exact rational_list_state_cobham

theorem verified_encoded_rational_list_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedRationalListParser (v 0) := by
  exact encoded_rational_list_parser_cobham

theorem verified_encoded_rational_list_parser_mem_fp : encodedRationalListParser ∈ FP := by
  exact encoded_rational_list_parser_mem_fp

theorem verified_decode_fraction_payloads_code (fuel : ℕ) (payloads : List (List Bool))
    (h : (payloadListCode payloads).length ≤ fuel) :
    decodeFractionPayloads fuel (payloadListCode payloads)=payloads.map fractionWordValue := by
  exact decode_fraction_payloads_code fuel payloads h

theorem verified_rational_list_state_result_pack (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    rationalListStateResult (countedPack count [valid] rest (payloadListCode payloads))=
      if wordValue count=0 ∧ valid=true then some ((payloads.map fractionWordValue).reverse,rest) else none := by
  exact rational_list_state_result_pack count rest valid payloads

theorem verified_rational_list_iterate_run (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    (rationalListStep^[fuel]) (countedPack count [valid] rest (payloadListCode payloads))=
      rationalListRun fuel count valid rest payloads := by
  exact rational_list_iterate_run fuel count rest valid payloads

theorem verified_read_rational_of_flag_true (input : List Bool)
    (h : Complexity.pairFst (encodedRationalParser input)=[true]) :
    IV04.Paper.readRational input=some
      (fractionWordValue (Complexity.pairFst (Complexity.pairSnd (encodedRationalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input))) := by
  exact read_rational_of_flag_true input h

theorem verified_read_rational_of_flag_false (input : List Bool)
    (h : Complexity.pairFst (encodedRationalParser input)=[false]) :
    IV04.Paper.readRational input=none := by
  exact read_rational_of_flag_false input h

theorem verified_rational_list_run_result (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    rationalListStateResult (rationalListRun fuel count valid rest payloads)=
      if valid then (fuelReadRationals fuel (wordValue count) rest).map
        (fun x => ((payloads.map fractionWordValue).reverse ++ x.1,x.2)) else none := by
  exact rational_list_run_result fuel count rest valid payloads

theorem verified_rational_list_state_flag_boolean (input : List Bool) :
    countedFlag (rationalListState input)=[true] ∨ countedFlag (rationalListState input)=[false] := by
  exact rational_list_state_flag_boolean input

theorem verified_rational_list_parser_result_eq_state (input : List Bool) :
    rationalListParserResult input=rationalListStateResult (rationalListState input) := by
  exact rational_list_parser_result_eq_state input

theorem verified_rational_list_parser_exact (input : List Bool) :
    rationalListParserResult input=readRationals (wordValue (pairFst input)) (pairSnd input) := by
  exact rational_list_parser_exact input

theorem verified_rational_list_parser_actual_polytime : encodedRationalListParser ∈ FP ∧
    ∀ input, rationalListParserResult input=readRationals (wordValue (pairFst input)) (pairSnd input) := by
  exact rational_list_parser_actual_polytime

theorem verified_read_rationals_codes (values : List ℚ) (tail : List Bool) :
    readRationals values.length (values.flatMap IV04.Paper.rationalCode ++ tail)=some (values,tail) := by
  exact read_rationals_codes values tail

theorem verified_rational_list_parser_actual_codes (values : List ℚ) (tail : List Bool) :
    rationalListParserResult (pair values.length.bits (values.flatMap IV04.Paper.rationalCode ++ tail))=
      some (values,tail) := by
  exact rational_list_parser_actual_codes values tail

theorem verified_rational_list_run_payload_shape (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool))
    (hpositive : ∀ w ∈ payloads, 0 < wordValue (pairSnd w)) :
    ∃ c b r ps, rationalListRun fuel count valid rest payloads=countedPack c [b] r (payloadListCode ps) ∧
      ∀ w ∈ ps, 0 < wordValue (pairSnd w) := by
  exact rational_list_run_payload_shape fuel count rest valid payloads hpositive

theorem verified_rational_list_state_payload_shape (input : List Bool) :
    ∃ c b r ps, rationalListState input=countedPack c [b] r (payloadListCode ps) ∧
      ∀ w ∈ ps, 0 < wordValue (pairSnd w) := by
  exact rational_list_state_payload_shape input

theorem verified_rational_list_parser_payload_shape (input : List Bool) :
    ∃ b ps rest, encodedRationalListParser input=pair [b] (pair (payloadListCode ps) rest) ∧
      ∀ w ∈ ps, 0 < wordValue (pairSnd w) := by
  exact rational_list_parser_payload_shape input

#print axioms IV04.Paper.Computational.verified_natural_parser_payload_tail_budget
#print axioms IV04.Paper.Computational.verified_rational_parser_flag_boolean
#print axioms IV04.Paper.Computational.verified_rational_parser_tail_length
#print axioms IV04.Paper.Computational.verified_rational_parser_raw_payload_budget
#print axioms IV04.Paper.Computational.verified_rational_parser_fraction_length
#print axioms IV04.Paper.Computational.verified_rational_parser_success_budget
#print axioms IV04.Paper.Computational.verified_read_rational_consumes_bits
#print axioms IV04.Paper.Computational.verified_fuel_read_rationals_exact
#print axioms IV04.Paper.Computational.verified_rational_list_step_pack
#print axioms IV04.Paper.Computational.verified_rational_list_step_shape
#print axioms IV04.Paper.Computational.verified_rational_list_iterate_shape
#print axioms IV04.Paper.Computational.verified_rational_list_iterate_length
#print axioms IV04.Paper.Computational.verified_rational_list_initial_iterate_length
#print axioms IV04.Paper.Computational.verified_rational_list_state_length
#print axioms IV04.Paper.Computational.verified_rational_list_step_cobham
#print axioms IV04.Paper.Computational.verified_rational_list_initial_cobham
#print axioms IV04.Paper.Computational.verified_rational_list_state_cobham
#print axioms IV04.Paper.Computational.verified_encoded_rational_list_parser_cobham
#print axioms IV04.Paper.Computational.verified_encoded_rational_list_parser_mem_fp
#print axioms IV04.Paper.Computational.verified_decode_fraction_payloads_code
#print axioms IV04.Paper.Computational.verified_rational_list_state_result_pack
#print axioms IV04.Paper.Computational.verified_rational_list_iterate_run
#print axioms IV04.Paper.Computational.verified_read_rational_of_flag_true
#print axioms IV04.Paper.Computational.verified_read_rational_of_flag_false
#print axioms IV04.Paper.Computational.verified_rational_list_run_result
#print axioms IV04.Paper.Computational.verified_rational_list_state_flag_boolean
#print axioms IV04.Paper.Computational.verified_rational_list_parser_result_eq_state
#print axioms IV04.Paper.Computational.verified_rational_list_parser_exact
#print axioms IV04.Paper.Computational.verified_rational_list_parser_actual_polytime
#print axioms IV04.Paper.Computational.verified_read_rationals_codes
#print axioms IV04.Paper.Computational.verified_rational_list_parser_actual_codes
#print axioms IV04.Paper.Computational.verified_rational_list_run_payload_shape
#print axioms IV04.Paper.Computational.verified_rational_list_state_payload_shape
#print axioms IV04.Paper.Computational.verified_rational_list_parser_payload_shape
end IV04.Paper.Computational
