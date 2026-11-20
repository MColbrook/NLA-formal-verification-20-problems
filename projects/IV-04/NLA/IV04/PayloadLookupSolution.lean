module

public import NLA.IV04.PaperPayloadLookupSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem verified_polynomial_payload_lookup_mem_fp : polynomialPayloadLookup ∈ FP := by
  exact polynomial_payload_lookup_mem_fp

theorem verified_polynomial_payload_lookup_length (input : List Bool) :
    (polynomialPayloadLookup input).length ≤ (pairSnd input).length := by
  exact polynomial_payload_lookup_length input

theorem verified_payload_lookup_iterate_length (k : ℕ) (input : List Bool) :
    ((payloadLookupStep^[k]) (pair (pairFst input) (pairSnd input))).length ≤ 2*input.length+2 := by
  exact payload_lookup_iterate_length k input

theorem verified_payload_lookup_word_code (rows : List (List Bool)) (index : List Bool)
    (hr : wordValue index < rows.length) :
    polynomialPayloadLookup (pair index (payloadListCode rows))=rows[wordValue index] := by
  exact payload_lookup_word_code rows index hr

theorem verified_payload_lookup_word_past_end (rows : List (List Bool)) (index : List Bool)
    (hr : rows.length ≤ wordValue index) :
    polynomialPayloadLookup (pair index (payloadListCode rows))=[] := by
  exact payload_lookup_word_past_end rows index hr

#print axioms IV04.Paper.Computational.verified_polynomial_payload_lookup_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_payload_lookup_length
#print axioms IV04.Paper.Computational.verified_payload_lookup_iterate_length
#print axioms IV04.Paper.Computational.verified_payload_lookup_word_code
#print axioms IV04.Paper.Computational.verified_payload_lookup_word_past_end
end IV04.Paper.Computational
