module

public import NLA.IV04.PaperNaturalParserSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_header_word_length (input : List Bool) :
    (headerWord input).length ≤ input.length := by
  exact header_word_length input

theorem verified_header_word_header (n : ℕ) (tail : List Bool) :
    headerWord (List.replicate n true ++ false :: tail)=List.replicate n true := by
  exact header_word_header n tail

theorem verified_header_word_cobham :
    Cobham fun v : Fin 1 → List Bool => headerWord (v 0) := by
  exact header_word_cobham

theorem verified_natural_parse_rest_cobham :
    Cobham fun v : Fin 1 → List Bool => naturalParseRest (v 0) := by
  exact natural_parse_rest_cobham

theorem verified_natural_parse_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => naturalParseFlag (v 0) := by
  exact natural_parse_flag_cobham

theorem verified_encoded_natural_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedNaturalParser (v 0) := by
  exact encoded_natural_parser_cobham

theorem verified_encoded_natural_parser_mem_fp : encodedNaturalParser ∈ FP := by
  exact encoded_natural_parser_mem_fp

theorem verified_read_unary_stages (input : List Bool) :
    IV04.Paper.readUnary input=
      if input.drop (headerWord input).length=[] then none
      else some ((headerWord input).length,naturalParseRest input) := by
  exact read_unary_stages input

theorem verified_natural_parse_flag_stages (input : List Bool) :
    naturalParseFlag input=
      if input.drop (headerWord input).length=[] then [false]
      else if (headerWord input).length ≤ (naturalParseRest input).length then [true] else [false] := by
  exact natural_parse_flag_stages input

theorem verified_read_natural_stages (input : List Bool) :
    IV04.Paper.readNatural input=
      if input.drop (headerWord input).length=[] then none
      else if (headerWord input).length ≤ (naturalParseRest input).length
      then some (wordValue ((naturalParseRest input).take (headerWord input).length),
        (naturalParseRest input).drop (headerWord input).length)
      else none := by
  exact read_natural_stages input

theorem verified_natural_parser_flag (input : List Bool) :
    Complexity.pairFst (encodedNaturalParser input)=naturalParseFlag input := by
  exact natural_parser_flag input

theorem verified_natural_parser_payload (input : List Bool) :
    Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))=
      (naturalParseRest input).take (headerWord input).length := by
  exact natural_parser_payload input

theorem verified_natural_parser_tail (input : List Bool) :
    Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))=
      (naturalParseRest input).drop (headerWord input).length := by
  exact natural_parser_tail input

theorem verified_natural_parser_exact (input : List Bool) :
    (if Complexity.pairFst (encodedNaturalParser input)=[true] then
      some (wordValue (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input)))
      else none)=IV04.Paper.readNatural input := by
  exact natural_parser_exact input

theorem verified_natural_parser_actual_polytime : encodedNaturalParser ∈ FP ∧
    ∀ input,
    (if Complexity.pairFst (encodedNaturalParser input)=[true] then
      some (wordValue (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input)))
      else none)=IV04.Paper.readNatural input := by
  exact natural_parser_actual_polytime

#print axioms IV04.Paper.Computational.verified_header_word_length
#print axioms IV04.Paper.Computational.verified_header_word_header
#print axioms IV04.Paper.Computational.verified_header_word_cobham
#print axioms IV04.Paper.Computational.verified_natural_parse_rest_cobham
#print axioms IV04.Paper.Computational.verified_natural_parse_flag_cobham
#print axioms IV04.Paper.Computational.verified_encoded_natural_parser_cobham
#print axioms IV04.Paper.Computational.verified_encoded_natural_parser_mem_fp
#print axioms IV04.Paper.Computational.verified_read_unary_stages
#print axioms IV04.Paper.Computational.verified_natural_parse_flag_stages
#print axioms IV04.Paper.Computational.verified_read_natural_stages
#print axioms IV04.Paper.Computational.verified_natural_parser_flag
#print axioms IV04.Paper.Computational.verified_natural_parser_payload
#print axioms IV04.Paper.Computational.verified_natural_parser_tail
#print axioms IV04.Paper.Computational.verified_natural_parser_exact
#print axioms IV04.Paper.Computational.verified_natural_parser_actual_polytime
end IV04.Paper.Computational
