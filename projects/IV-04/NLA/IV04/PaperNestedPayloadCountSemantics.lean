module

public import NLA.IV04.PaperNestedPayloadCountPoly
public import NLA.IV04.PaperPayloadCountSemantics
public import NLA.IV04.PaperSATCNFPayloadDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

 theorem nested_payload_count_iterate_nil (k : ℕ) (total : List Bool) :
    (nestedPayloadCountStep^[k]) (pair [] total)=pair [] total := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,nested_payload_count_step_pair];simp

 theorem nested_payload_count_iteration_value (k : ℕ)
    (payloads : List (List (List Bool))) (total : List Bool) (h : payloads.length ≤ k) :
    wordValue (pairSnd ((nestedPayloadCountStep^[k])
      (pair (payloadListCode (payloads.map payloadListCode)) total)))=
      wordValue total+(payloads.map List.length).sum := by
  induction k generalizing payloads total with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,nested_payload_count_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h;omega
      rw [Function.iterate_succ_apply,nested_payload_count_step_pair]
      have hn : pair (payloadListCode payload) (payloadListCode (payloads.map payloadListCode))≠[] := by
        intro he
        have hl := congrArg List.length he
        simp only [pair_length,List.length_nil] at hl
        omega
      simp only [List.map_cons,payloadListCode,hn,if_false,pairSnd_pair,pairFst_pair]
      rw [ih payloads (polynomialWordAdd total
        (polynomialPayloadCount (payloadListCode payload))) ht,polynomial_word_add_value,
        polynomial_payload_count_value]
      simp only [List.map_cons,List.sum_cons]
      omega

 theorem polynomial_nested_payload_count_exact (payloads : List (List (List Bool))) :
    polynomialNestedPayloadCount (payloadListCode (payloads.map payloadListCode))=
      (payloads.map List.length).sum.bits := by
  have hh := payload_list_count_length (payloads.map payloadListCode)
  simp only [List.length_map] at hh
  have h := nested_payload_count_iteration_value
    (payloadListCode (payloads.map payloadListCode)).length payloads [] hh
  simp only [wordValue,Nat.zero_add] at h
  simp only [polynomialNestedPayloadCount,canonical_word_eq_bits]
  rw [show wordValue (pairSnd (nestedPayloadCountState
    (payloadListCode (payloads.map payloadListCode))))=(payloads.map List.length).sum from h]

 theorem sat_formula_payload_literal_count (formula : SAT.CNF) :
    polynomialNestedPayloadCount (satFormulaPayload formula)=formula.flatten.length.bits := by
  have h := polynomial_nested_payload_count_exact
    (formula.map fun clause => clause.reverse.map satLiteralPayload)
  simpa [satFormulaPayload,satClausePayload,List.map_map,Function.comp_def,
    List.length_flatten] using h

 theorem nested_payload_count_actual_polytime : polynomialNestedPayloadCount ∈ FP ∧
    (∀ input, (polynomialNestedPayloadCount input).length ≤ 7*input.length+2) ∧
    (∀ formula, polynomialNestedPayloadCount (satFormulaPayload formula)=formula.flatten.length.bits) :=
  ⟨polynomial_nested_payload_count_mem_fp,polynomial_nested_payload_count_length,
    sat_formula_payload_literal_count⟩

#print axioms sat_formula_payload_literal_count
#print axioms nested_payload_count_actual_polytime
end IV04.Paper.Computational
