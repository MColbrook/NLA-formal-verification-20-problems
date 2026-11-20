module

public import NLA.IV04.PaperSATMetadataSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace IV04.Paper.Computational
open Complexity SATReduction

theorem verified_payload_count_clock_length (clock input : List Bool) :
    ((payloadCountStep^[clock.length]) (pair input [])).length ≤
      2*input.length+2+2*clock.length := by
  exact payload_count_clock_length clock input

theorem verified_polynomial_payload_count_mem_fp : polynomialPayloadCount ∈ FP := by
  exact polynomial_payload_count_mem_fp

theorem verified_polynomial_payload_count_exact (payloads : List (List Bool)) :
    polynomialPayloadCount (payloadListCode payloads)=payloads.length.bits := by
  exact polynomial_payload_count_exact payloads

theorem verified_payload_count_actual_polytime : polynomialPayloadCount ∈ FP ∧
    (∀ input, (polynomialPayloadCount input).length ≤ 4*input.length+2) ∧
    (∀ payloads, polynomialPayloadCount (payloadListCode payloads)=payloads.length.bits) := by
  exact payload_count_actual_polytime

theorem verified_nested_payload_count_clock_length (clock input : List Bool) :
    ((nestedPayloadCountStep^[clock.length]) (pair input [])).length ≤
      4*input.length+2+3*clock.length := by
  exact nested_payload_count_clock_length clock input

theorem verified_polynomial_nested_payload_count_mem_fp : polynomialNestedPayloadCount ∈ FP := by
  exact polynomial_nested_payload_count_mem_fp

theorem verified_polynomial_nested_payload_count_exact (payloads : List (List (List Bool))) :
    polynomialNestedPayloadCount (payloadListCode (payloads.map payloadListCode))=
      (payloads.map List.length).sum.bits := by
  exact polynomial_nested_payload_count_exact payloads

theorem verified_sat_formula_payload_literal_count (formula : SAT.CNF) :
    polynomialNestedPayloadCount (satFormulaPayload formula)=formula.flatten.length.bits := by
  exact sat_formula_payload_literal_count formula

theorem verified_nested_payload_count_actual_polytime : polynomialNestedPayloadCount ∈ FP ∧
    (∀ input, (polynomialNestedPayloadCount input).length ≤ 7*input.length+2) ∧
    (∀ formula, polynomialNestedPayloadCount (satFormulaPayload formula)=formula.flatten.length.bits) := by
  exact nested_payload_count_actual_polytime

theorem verified_polynomial_word_max_value (left right : List Bool) :
    wordValue (polynomialWordMax left right)=max (wordValue left) (wordValue right) := by
  exact polynomial_word_max_value left right

theorem verified_polynomial_payload_word_max_exact (select : List Bool → List Bool)
    (payloads : List (List Bool)) :
    polynomialPayloadWordMax select (payloadListCode payloads)=
      ((payloads.map fun p => wordValue (select p)).foldr max 0).bits := by
  exact polynomial_payload_word_max_exact select payloads

theorem verified_polynomial_sat_clause_maximum_length (input : List Bool) :
    (polynomialSATClauseMaximum input).length ≤ 2*input.length+2 := by
  exact polynomial_sat_clause_maximum_length input

theorem verified_polynomial_sat_formula_maximum_length (input : List Bool) :
    (polynomialSATFormulaMaximum input).length ≤ 4*input.length+2 := by
  exact polynomial_sat_formula_maximum_length input

theorem verified_polynomial_sat_metadata_mem_fp : polynomialSATMetadata ∈ FP := by
  exact polynomial_sat_metadata_mem_fp

theorem verified_polynomial_sat_input_metadata_mem_fp : polynomialSATInputMetadata ∈ FP := by
  exact polynomial_sat_input_metadata_mem_fp

theorem verified_polynomial_sat_clause_maximum_exact (clause : SAT.Clause) :
    polynomialSATClauseMaximum (satClausePayload clause)=clause.maxVar.bits := by
  exact polynomial_sat_clause_maximum_exact clause

theorem verified_polynomial_sat_formula_maximum_exact (formula : SAT.CNF) :
    polynomialSATFormulaMaximum (satFormulaPayload formula)=formula.maxVar.bits := by
  exact polynomial_sat_formula_maximum_exact formula

theorem verified_polynomial_sat_metadata_exact (formula : SAT.CNF) :
    polynomialSATMetadata (satFormulaPayload formula)=
      pair (satVariables formula).bits (pair formula.length.bits (satLiteralBudget formula).bits) := by
  exact polynomial_sat_metadata_exact formula

theorem verified_polynomial_sat_input_metadata_exact (bits : List Bool) (formula : SAT.CNF)
    (h : SAT.CNF.decode? bits=some formula) :
    polynomialSATInputMetadata bits=pair [true]
      (pair (satVariables formula).bits (pair formula.length.bits (satLiteralBudget formula).bits)) := by
  exact polynomial_sat_input_metadata_exact bits formula h

theorem verified_polynomial_sat_input_metadata_reject (bits : List Bool) (h : SAT.CNF.decode? bits=none) :
    pairFst (polynomialSATInputMetadata bits)=[false] := by
  exact polynomial_sat_input_metadata_reject bits h

theorem verified_sat_input_metadata_actual_polytime : polynomialSATInputMetadata ∈ FP ∧
    (∀ bits formula, SAT.CNF.decode? bits=some formula → polynomialSATInputMetadata bits=pair [true]
      (pair (satVariables formula).bits (pair formula.length.bits (satLiteralBudget formula).bits))) ∧
    (∀ bits, SAT.CNF.decode? bits=none → pairFst (polynomialSATInputMetadata bits)=[false]) := by
  exact sat_input_metadata_actual_polytime

end IV04.Paper.Computational
end

#print axioms IV04.Paper.Computational.verified_payload_count_clock_length
#print axioms IV04.Paper.Computational.verified_polynomial_payload_count_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_payload_count_exact
#print axioms IV04.Paper.Computational.verified_payload_count_actual_polytime
#print axioms IV04.Paper.Computational.verified_nested_payload_count_clock_length
#print axioms IV04.Paper.Computational.verified_polynomial_nested_payload_count_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_nested_payload_count_exact
#print axioms IV04.Paper.Computational.verified_sat_formula_payload_literal_count
#print axioms IV04.Paper.Computational.verified_nested_payload_count_actual_polytime
#print axioms IV04.Paper.Computational.verified_polynomial_word_max_value
#print axioms IV04.Paper.Computational.verified_polynomial_payload_word_max_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_clause_maximum_length
#print axioms IV04.Paper.Computational.verified_polynomial_sat_formula_maximum_length
#print axioms IV04.Paper.Computational.verified_polynomial_sat_metadata_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_sat_input_metadata_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_sat_clause_maximum_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_formula_maximum_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_metadata_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_input_metadata_exact
#print axioms IV04.Paper.Computational.verified_polynomial_sat_input_metadata_reject
#print axioms IV04.Paper.Computational.verified_sat_input_metadata_actual_polytime
