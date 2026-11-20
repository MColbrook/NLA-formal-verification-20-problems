module

public import NLA.IV04.PaperRationalParserPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_canonical_word_eq_nil (bits : List Bool) : canonicalWord bits=[] ↔ wordValue bits=0 := by
  exact canonical_word_eq_nil bits

theorem verified_normalize_fraction_word_cases (input : List Bool) :
    normalizeFractionWord input=
      if wordValue (Complexity.pairSnd input)=0 then Complexity.pair [false] [true]
      else Complexity.pair (Complexity.pairFst input) (canonicalWord (Complexity.pairSnd input)) := by
  exact normalize_fraction_word_cases input

theorem verified_normalize_fraction_denominator_positive (input : List Bool) :
    0 < wordValue (Complexity.pairSnd (normalizeFractionWord input)) := by
  exact normalize_fraction_denominator_positive input

theorem verified_normalize_fraction_word_value (input : List Bool) :
    fractionWordValue (normalizeFractionWord input)=fractionWordValue input := by
  exact normalize_fraction_word_value input

theorem verified_positive_signed_word_value (bits : List Bool) :
    signedWordValue (false :: bits)=(wordValue bits : ℤ) := by
  exact positive_signed_word_value bits

theorem verified_polynomial_fraction_add_value (left right : List Bool) :
    fractionWordValue (polynomialFractionAdd left right)=fractionWordValue left+fractionWordValue right := by
  exact polynomial_fraction_add_value left right

theorem verified_polynomial_fraction_multiply_value (left right : List Bool) :
    fractionWordValue (polynomialFractionMultiply left right)=fractionWordValue left*fractionWordValue right := by
  exact polynomial_fraction_multiply_value left right

theorem verified_polynomial_fraction_add_denominator_positive (left right : List Bool) :
    0 < wordValue (Complexity.pairSnd (polynomialFractionAdd left right)) := by
  exact polynomial_fraction_add_denominator_positive left right

theorem verified_polynomial_fraction_multiply_denominator_positive (left right : List Bool) :
    0 < wordValue (Complexity.pairSnd (polynomialFractionMultiply left right)) := by
  exact polynomial_fraction_multiply_denominator_positive left right

theorem verified_normalize_fraction_word_cobham :
    Cobham fun v : Fin 1 → List Bool => normalizeFractionWord (v 0) := by
  exact normalize_fraction_word_cobham

theorem verified_normalize_fraction_word_mem_fp : normalizeFractionWord ∈ FP := by
  exact normalize_fraction_word_mem_fp

theorem verified_polynomial_fraction_add_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialFractionAdd (v 0) (v 1) := by
  exact polynomial_fraction_add_cobham

theorem verified_polynomial_fraction_multiply_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialFractionMultiply (v 0) (v 1) := by
  exact polynomial_fraction_multiply_cobham

theorem verified_encoded_fraction_add_mem_fp : encodedPolynomialFractionAdd ∈ FP := by
  exact encoded_fraction_add_mem_fp

theorem verified_encoded_fraction_multiply_mem_fp : encodedPolynomialFractionMultiply ∈ FP := by
  exact encoded_fraction_multiply_mem_fp

theorem verified_normalize_fraction_actual_polytime : normalizeFractionWord ∈ FP ∧
    ∀ input, fractionWordValue (normalizeFractionWord input)=fractionWordValue input ∧
      0 < wordValue (pairSnd (normalizeFractionWord input)) := by
  exact normalize_fraction_actual_polytime

theorem verified_encoded_fraction_add_actual_polytime : encodedPolynomialFractionAdd ∈ FP ∧
    ∀ left right, fractionWordValue (encodedPolynomialFractionAdd (pair left right))=
      fractionWordValue left+fractionWordValue right := by
  exact encoded_fraction_add_actual_polytime

theorem verified_encoded_fraction_multiply_actual_polytime : encodedPolynomialFractionMultiply ∈ FP ∧
    ∀ left right, fractionWordValue (encodedPolynomialFractionMultiply (pair left right))=
      fractionWordValue left*fractionWordValue right := by
  exact encoded_fraction_multiply_actual_polytime

theorem verified_natural_parser_flag_boolean (input : List Bool) :
    Complexity.pairFst (encodedNaturalParser input)=[true] ∨
      Complexity.pairFst (encodedNaturalParser input)=[false] := by
  exact natural_parser_flag_boolean input

theorem verified_rational_parser_flag_stages (input : List Bool) :
    rationalParserFlag input=
      if input=[] then [false]
      else if Complexity.pairFst (rationalParserFirst input)=[true] ∧
        Complexity.pairFst (rationalParserSecond input)=[true] then [true] else [false] := by
  exact rational_parser_flag_stages input

theorem verified_rational_parser_flag (input : List Bool) :
    Complexity.pairFst (encodedRationalParser input)=rationalParserFlag input := by
  exact rational_parser_flag input

theorem verified_rational_parser_fraction (input : List Bool) :
    Complexity.pairFst (Complexity.pairSnd (encodedRationalParser input))=rationalParserFraction input := by
  exact rational_parser_fraction input

theorem verified_rational_parser_tail (input : List Bool) :
    Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input))=
      Complexity.pairSnd (Complexity.pairSnd (rationalParserSecond input)) := by
  exact rational_parser_tail input

theorem verified_rational_parser_denominator_positive (input : List Bool) :
    0 < wordValue (Complexity.pairSnd (rationalParserFraction input)) := by
  exact rational_parser_denominator_positive input

theorem verified_rational_parser_fraction_value (input : List Bool) :
    fractionWordValue (rationalParserFraction input)=
      ((if firstBit input then
          -(wordValue (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))) : ℤ)
        else (wordValue (Complexity.pairFst (Complexity.pairSnd (rationalParserFirst input))) : ℤ)) : ℚ)/
      (wordValue (Complexity.pairFst (Complexity.pairSnd (rationalParserSecond input))) : ℚ) := by
  exact rational_parser_fraction_value input

theorem verified_rational_parser_bind_identity (b : Bool) (first : List Bool)
    (parse : List Bool → List Bool) :
    (if (if Complexity.pairFst first=[true] ∧
        Complexity.pairFst (parse (Complexity.pairSnd (Complexity.pairSnd first)))=[true]
      then [true] else [false])=[true] then
      some ((if b then -((wordValue (Complexity.pairFst (Complexity.pairSnd first)) : ℤ) : ℚ)
        else ((wordValue (Complexity.pairFst (Complexity.pairSnd first)) : ℤ) : ℚ))/
        (wordValue (Complexity.pairFst (Complexity.pairSnd
          (parse (Complexity.pairSnd (Complexity.pairSnd first))))) : ℚ),
        Complexity.pairSnd (Complexity.pairSnd (parse (Complexity.pairSnd (Complexity.pairSnd first)))))
      else none)=
    (Option.bind (if Complexity.pairFst first=[true] then
        some (wordValue (Complexity.pairFst (Complexity.pairSnd first)),
          Complexity.pairSnd (Complexity.pairSnd first)) else none)
      (fun x => Option.bind (if Complexity.pairFst (parse x.2)=[true] then
        some (wordValue (Complexity.pairFst (Complexity.pairSnd (parse x.2))),
          Complexity.pairSnd (Complexity.pairSnd (parse x.2))) else none)
        (fun y =>
          let signed : ℤ := if b then -(x.1 : ℤ) else (x.1 : ℤ)
          some ((signed : ℚ)/(y.1 : ℚ),y.2)))) := by
  exact rational_parser_bind_identity b first parse

theorem verified_rational_parser_exact (input : List Bool) :
    (if Complexity.pairFst (encodedRationalParser input)=[true] then
      some (fractionWordValue (Complexity.pairFst (Complexity.pairSnd (encodedRationalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input)))
      else none)=IV04.Paper.readRational input := by
  exact rational_parser_exact input

theorem verified_rational_parser_first_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalParserFirst (v 0) := by
  exact rational_parser_first_cobham

theorem verified_rational_parser_second_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalParserSecond (v 0) := by
  exact rational_parser_second_cobham

theorem verified_rational_parser_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalParserFlag (v 0) := by
  exact rational_parser_flag_cobham

theorem verified_rational_parser_fraction_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalParserFraction (v 0) := by
  exact rational_parser_fraction_cobham

theorem verified_encoded_rational_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedRationalParser (v 0) := by
  exact encoded_rational_parser_cobham

theorem verified_encoded_rational_parser_mem_fp : encodedRationalParser ∈ FP := by
  exact encoded_rational_parser_mem_fp

theorem verified_rational_parser_actual_polytime : encodedRationalParser ∈ FP ∧
    ∀ input,
    (if pairFst (encodedRationalParser input)=[true] then
      some (fractionWordValue (pairFst (pairSnd (encodedRationalParser input))),
        pairSnd (pairSnd (encodedRationalParser input)))
      else none)=IV04.Paper.readRational input := by
  exact rational_parser_actual_polytime

#print axioms IV04.Paper.Computational.verified_canonical_word_eq_nil
#print axioms IV04.Paper.Computational.verified_normalize_fraction_word_cases
#print axioms IV04.Paper.Computational.verified_normalize_fraction_denominator_positive
#print axioms IV04.Paper.Computational.verified_normalize_fraction_word_value
#print axioms IV04.Paper.Computational.verified_positive_signed_word_value
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_add_value
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_multiply_value
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_add_denominator_positive
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_multiply_denominator_positive
#print axioms IV04.Paper.Computational.verified_normalize_fraction_word_cobham
#print axioms IV04.Paper.Computational.verified_normalize_fraction_word_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_add_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_multiply_cobham
#print axioms IV04.Paper.Computational.verified_encoded_fraction_add_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_fraction_multiply_mem_fp
#print axioms IV04.Paper.Computational.verified_normalize_fraction_actual_polytime
#print axioms IV04.Paper.Computational.verified_encoded_fraction_add_actual_polytime
#print axioms IV04.Paper.Computational.verified_encoded_fraction_multiply_actual_polytime
#print axioms IV04.Paper.Computational.verified_natural_parser_flag_boolean
#print axioms IV04.Paper.Computational.verified_rational_parser_flag_stages
#print axioms IV04.Paper.Computational.verified_rational_parser_flag
#print axioms IV04.Paper.Computational.verified_rational_parser_fraction
#print axioms IV04.Paper.Computational.verified_rational_parser_tail
#print axioms IV04.Paper.Computational.verified_rational_parser_denominator_positive
#print axioms IV04.Paper.Computational.verified_rational_parser_fraction_value
#print axioms IV04.Paper.Computational.verified_rational_parser_bind_identity
#print axioms IV04.Paper.Computational.verified_rational_parser_exact
#print axioms IV04.Paper.Computational.verified_rational_parser_first_cobham
#print axioms IV04.Paper.Computational.verified_rational_parser_second_cobham
#print axioms IV04.Paper.Computational.verified_rational_parser_flag_cobham
#print axioms IV04.Paper.Computational.verified_rational_parser_fraction_cobham
#print axioms IV04.Paper.Computational.verified_encoded_rational_parser_cobham
#print axioms IV04.Paper.Computational.verified_encoded_rational_parser_mem_fp
#print axioms IV04.Paper.Computational.verified_rational_parser_actual_polytime
end IV04.Paper.Computational
