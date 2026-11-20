module

public import NLA.IV04.PaperFractionCoefficientClearing
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_fraction_word_list_denominator_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionWordListDenominator (v 0) := by
  exact fraction_word_list_denominator_cobham

theorem verified_fraction_word_list_denominator_mem_fp : fractionWordListDenominator ∈ FP := by
  exact fraction_word_list_denominator_mem_fp

theorem verified_fraction_word_list_denominator_value (payloads : List (List Bool)) :
    wordValue (fractionWordListDenominator (payloadListCode payloads))=
      ((payloads.map pairSnd).map wordValue).prod := by
  exact fraction_word_list_denominator_value payloads

theorem verified_fraction_word_list_denominator_length (input : List Bool) :
    (fractionWordListDenominator input).length ≤ 8*input.length+7 := by
  exact fraction_word_list_denominator_length input

theorem verified_cleared_fraction_word_cobham :
    Cobham fun v : Fin 3 → List Bool => clearedFractionWord (v 0) (v 1) (v 2) := by
  exact cleared_fraction_word_cobham

theorem verified_cleared_fraction_word_value (prior fraction : List Bool) (payloads : List (List Bool)) :
    signedWordValue (clearedFractionWord prior fraction (payloadListCode payloads))=
      signedWordValue (pairFst fraction)*(wordValue prior : ℤ)*
        (((payloads.map pairSnd).map wordValue).prod : ℤ) := by
  exact cleared_fraction_word_value prior fraction payloads

theorem verified_cleared_fraction_word_length (prior fraction suffix : List Bool) :
    (clearedFractionWord prior fraction suffix).length ≤ fraction.length+prior.length+8*suffix.length+8 := by
  exact cleared_fraction_word_length prior fraction suffix

theorem verified_coefficient_pack_cobham {n : ℕ}
    {rest prior output : (Fin n → List Bool) → List Bool}
    (hr : Cobham rest) (hp : Cobham prior) (ho : Cobham output) :
    Cobham fun v => coefficientPack (rest v) (prior v) (output v) := by
  exact coefficient_pack_cobham hr hp ho

theorem verified_fraction_coefficient_step_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionCoefficientStep (v 0) := by
  exact fraction_coefficient_step_cobham

theorem verified_fraction_coefficient_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionCoefficientInitial (v 0) := by
  exact fraction_coefficient_initial_cobham

theorem verified_fraction_coefficient_step_pack (rest prior output : List Bool) :
    fractionCoefficientStep (coefficientPack rest prior output)=
      if rest=[] then coefficientPack rest prior output else
        coefficientPack (pairSnd rest) (canonicalWordMultiply prior (pairSnd (pairFst rest)))
          (pair (clearedFractionWord prior (pairFst rest) (pairSnd rest)) output) := by
  exact fraction_coefficient_step_pack rest prior output

theorem verified_fraction_coefficient_step_shape (rest prior output : List Bool) :
    ∃ r p o : List Bool, fractionCoefficientStep (coefficientPack rest prior output)=coefficientPack r p o ∧
      r.length+p.length ≤ rest.length+prior.length ∧
      o.length ≤ output.length+18*(rest.length+prior.length)+18 := by
  exact fraction_coefficient_step_shape rest prior output

theorem verified_fraction_coefficient_iterate_shape (k : ℕ) (rest prior output : List Bool) :
    ∃ r p o : List Bool, (fractionCoefficientStep^[k]) (coefficientPack rest prior output)=coefficientPack r p o ∧
      r.length+p.length ≤ rest.length+prior.length ∧
      o.length ≤ output.length+k*(18*(rest.length+prior.length)+18) := by
  exact fraction_coefficient_iterate_shape k rest prior output

theorem verified_fraction_coefficient_iterate_length (k : ℕ) (rest prior output : List Bool) :
    ((fractionCoefficientStep^[k]) (coefficientPack rest prior output)).length ≤
      2*(rest.length+prior.length)+output.length+4+k*(18*(rest.length+prior.length)+18) := by
  exact fraction_coefficient_iterate_length k rest prior output

theorem verified_fraction_coefficient_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((fractionCoefficientStep^[k]) (fractionCoefficientInitial input)).length ≤
      2*input.length+6+k*(18*input.length+36) := by
  exact fraction_coefficient_initial_iterate_length k input

theorem verified_fraction_coefficient_state_length (input : List Bool) :
    (fractionCoefficientState input).length ≤ 2*input.length+6+input.length*(18*input.length+36) := by
  exact fraction_coefficient_state_length input

theorem verified_fraction_coefficient_state_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionCoefficientState (v 0) := by
  exact fraction_coefficient_state_cobham

theorem verified_polynomial_fraction_coefficients_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialFractionCoefficients (v 0) := by
  exact polynomial_fraction_coefficients_cobham

theorem verified_polynomial_fraction_coefficients_mem_fp : polynomialFractionCoefficients ∈ FP := by
  exact polynomial_fraction_coefficients_mem_fp

theorem verified_encoded_rational_list_clearing_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedRationalListClearing (v 0) := by
  exact encoded_rational_list_clearing_cobham

theorem verified_encoded_rational_list_clearing_mem_fp : encodedRationalListClearing ∈ FP := by
  exact encoded_rational_list_clearing_mem_fp

theorem verified_fraction_coefficient_iterate_nil (k : ℕ) (prior output : List Bool) :
    (fractionCoefficientStep^[k]) (coefficientPack [] prior output)=coefficientPack [] prior output := by
  exact fraction_coefficient_iterate_nil k prior output

theorem verified_fraction_coefficient_iterate_code (k : ℕ) (prior : List Bool)
    (fractions output : List (List Bool)) (h : fractions.length ≤ k) :
    (fractionCoefficientStep^[k]) (coefficientPack (payloadListCode fractions) prior (payloadListCode output))=
      coefficientPack [] (coefficientFinalPrior prior fractions)
        (payloadListCode ((coefficientWords prior fractions).reverse ++ output)) := by
  exact fraction_coefficient_iterate_code k prior fractions output h

theorem verified_fraction_coefficients_code (fractions : List (List Bool)) :
    polynomialFractionCoefficients (payloadListCode fractions)=
      payloadListCode ((coefficientWords [true] fractions).reverse) := by
  exact fraction_coefficients_code fractions

theorem verified_coefficient_words_length (prior : List Bool) (fractions : List (List Bool)) :
    (coefficientWords prior fractions).length=fractions.length := by
  exact coefficient_words_length prior fractions

theorem verified_coefficient_final_prior_value (prior : List Bool) (fractions : List (List Bool)) :
    wordValue (coefficientFinalPrior prior fractions)=wordValue prior*fractionDenominatorProduct fractions := by
  exact coefficient_final_prior_value prior fractions

theorem verified_coefficient_words_rational_values (prior : List Bool) (fractions : List (List Bool))
    (hp : ∀ w ∈ fractions, 0 < wordValue (pairSnd w)) :
    (coefficientWords prior fractions).map (fun w => (signedWordValue w : ℚ))=
      fractions.map (fun w => fractionWordValue w * ((wordValue prior*fractionDenominatorProduct fractions : ℕ) : ℚ)) := by
  exact coefficient_words_rational_values prior fractions hp

theorem verified_fraction_coefficients_rational_values (fractions : List (List Bool))
    (hp : ∀ w ∈ fractions, 0 < wordValue (pairSnd w)) :
    ((coefficientWords [true] fractions).reverse).map (fun w => (signedWordValue w : ℚ))=
      ((fractions.map fractionWordValue).reverse).map (fun q => q*(fractionDenominatorProduct fractions : ℚ)) := by
  exact fraction_coefficients_rational_values fractions hp

theorem verified_rational_list_clearing_payload_shape (input : List Bool) :
    ∃ b fractions tail,
      encodedRationalListParser input=pair [b] (pair (payloadListCode fractions) tail) ∧
      (∀ w ∈ fractions, 0 < wordValue (pairSnd w)) ∧
      encodedRationalListClearing input=pair [b]
        (pair (polynomialRationalListDenominator input)
          (pair (payloadListCode ((coefficientWords [true] fractions).reverse)) tail)) ∧
      ((coefficientWords [true] fractions).reverse).map (fun w => (signedWordValue w : ℚ))=
        ((fractions.map fractionWordValue).reverse).map
          (fun q => q*(wordValue (polynomialRationalListDenominator input) : ℚ)) := by
  exact rational_list_clearing_payload_shape input

theorem verified_rational_list_parser_result_shape (input : List Bool) (b : Bool)
    (fractions : List (List Bool)) (tail : List Bool)
    (h : encodedRationalListParser input=pair [b] (pair (payloadListCode fractions) tail)) :
    rationalListParserResult input=
      if b then some ((fractions.map fractionWordValue).reverse,tail) else none := by
  exact rational_list_parser_result_shape input b fractions tail h

theorem verified_rational_list_clearing_correct (input : List Bool) (values : List ℚ) (tail : List Bool)
    (h : readRationals (wordValue (pairFst input)) (pairSnd input)=some (values,tail)) :
    ∃ denominator coefficients,
      encodedRationalListClearing input=pair [true]
        (pair denominator (pair (payloadListCode coefficients) tail)) ∧
      0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        values.map (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=values.length := by
  exact rational_list_clearing_correct input values tail h

theorem verified_rational_list_clearing_actual_codes (values : List ℚ) (tail : List Bool) :
    ∃ denominator coefficients,
      encodedRationalListClearing (pair values.length.bits (values.flatMap IV04.Paper.rationalCode ++ tail))=
        pair [true] (pair denominator (pair (payloadListCode coefficients) tail)) ∧
      0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        values.map (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=values.length := by
  exact rational_list_clearing_actual_codes values tail

theorem verified_rational_list_clearing_failure (input : List Bool)
    (h : readRationals (wordValue (pairFst input)) (pairSnd input)=none) :
    pairFst (encodedRationalListClearing input)=[false] := by
  exact rational_list_clearing_failure input h

theorem verified_rational_list_clearing_actual_polytime : encodedRationalListClearing ∈ FP ∧
    ∀ input values tail,
      readRationals (wordValue (pairFst input)) (pairSnd input)=some (values,tail) →
      ∃ denominator coefficients,
        encodedRationalListClearing input=pair [true]
          (pair denominator (pair (payloadListCode coefficients) tail)) ∧
        0 < wordValue denominator ∧
        coefficients.map (fun w => (signedWordValue w : ℚ))=
          values.map (fun q => q*(wordValue denominator : ℚ)) ∧
        coefficients.length=values.length := by
  exact rational_list_clearing_actual_polytime

#print axioms IV04.Paper.Computational.verified_fraction_word_list_denominator_cobham
#print axioms IV04.Paper.Computational.verified_fraction_word_list_denominator_mem_fp
#print axioms IV04.Paper.Computational.verified_fraction_word_list_denominator_value
#print axioms IV04.Paper.Computational.verified_fraction_word_list_denominator_length
#print axioms IV04.Paper.Computational.verified_cleared_fraction_word_cobham
#print axioms IV04.Paper.Computational.verified_cleared_fraction_word_value
#print axioms IV04.Paper.Computational.verified_cleared_fraction_word_length
#print axioms IV04.Paper.Computational.verified_coefficient_pack_cobham
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_step_cobham
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_initial_cobham
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_step_pack
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_step_shape
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_iterate_shape
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_iterate_length
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_initial_iterate_length
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_state_length
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_state_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_coefficients_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_coefficients_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_rational_list_clearing_cobham
#print axioms IV04.Paper.Computational.verified_encoded_rational_list_clearing_mem_fp
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_iterate_nil
#print axioms IV04.Paper.Computational.verified_fraction_coefficient_iterate_code
#print axioms IV04.Paper.Computational.verified_fraction_coefficients_code
#print axioms IV04.Paper.Computational.verified_coefficient_words_length
#print axioms IV04.Paper.Computational.verified_coefficient_final_prior_value
#print axioms IV04.Paper.Computational.verified_coefficient_words_rational_values
#print axioms IV04.Paper.Computational.verified_fraction_coefficients_rational_values
#print axioms IV04.Paper.Computational.verified_rational_list_clearing_payload_shape
#print axioms IV04.Paper.Computational.verified_rational_list_parser_result_shape
#print axioms IV04.Paper.Computational.verified_rational_list_clearing_correct
#print axioms IV04.Paper.Computational.verified_rational_list_clearing_actual_codes
#print axioms IV04.Paper.Computational.verified_rational_list_clearing_failure
#print axioms IV04.Paper.Computational.verified_rational_list_clearing_actual_polytime
end IV04.Paper.Computational
