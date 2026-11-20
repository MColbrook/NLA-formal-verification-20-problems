module

public import NLA.IV04.PaperMatrixCoefficientInputPoly
public import NLA.IV04.PaperRationalParserBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem matrix_dimension_word_length (input : List Bool) :
    (matrixDimensionWord input).length ≤ input.length := by
  have hp := natural_parser_payload_tail_budget input
  have hc := canonical_word_length (pairFst (pairSnd (encodedNaturalParser input)))
  change (canonicalWord (pairFst (pairSnd (encodedNaturalParser input)))).length ≤ _
  omega

theorem matrix_rational_field_input_length (input : List Bool) :
    (matrixRationalFieldInput input).length ≤ 4*input.length+8 := by
  have hp := natural_parser_payload_tail_budget input
  have hc := matrix_field_count_word_length (pairFst (pairSnd (encodedNaturalParser input)))
  simp only [matrixRationalFieldInput,pair_length]
  omega

#print axioms matrix_rational_field_input_length
end IV04.Paper.Computational
