module

public import NLA.IV04.PaperFractionCoefficientSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem fraction_coefficients_rational_values (fractions : List (List Bool))
    (hp : ∀ w ∈ fractions, 0 < wordValue (pairSnd w)) :
    ((coefficientWords [true] fractions).reverse).map (fun w => (signedWordValue w : ℚ))=
      ((fractions.map fractionWordValue).reverse).map (fun q => q*(fractionDenominatorProduct fractions : ℚ)) := by
  have hc := coefficient_words_rational_values [true] fractions hp
  have hone : wordValue [true]=1 := rfl
  rw [hone,one_mul] at hc
  simp only [List.map_reverse,hc,List.map_map]
  rfl

theorem rational_list_clearing_payload_shape (input : List Bool) :
    ∃ b fractions tail,
      encodedRationalListParser input=pair [b] (pair (payloadListCode fractions) tail) ∧
      (∀ w ∈ fractions, 0 < wordValue (pairSnd w)) ∧
      encodedRationalListClearing input=pair [b]
        (pair (polynomialRationalListDenominator input)
          (pair (payloadListCode ((coefficientWords [true] fractions).reverse)) tail)) ∧
      ((coefficientWords [true] fractions).reverse).map (fun w => (signedWordValue w : ℚ))=
        ((fractions.map fractionWordValue).reverse).map
          (fun q => q*(wordValue (polynomialRationalListDenominator input) : ℚ)) := by
  obtain ⟨b,ps,tail,he,hp⟩ := rational_list_parser_payload_shape input
  have hd : wordValue (polynomialRationalListDenominator input)=fractionDenominatorProduct ps := by
    simp only [polynomialRationalListDenominator,he,pairFst_pair,pairSnd_pair,canonical_word_value,
      fraction_list_denominators_code,polynomial_word_list_product_value,List.map_reverse,
      List.prod_reverse,fractionDenominatorProduct]
  refine ⟨b,ps,tail,he,hp,?_,?_⟩
  · simp only [encodedRationalListClearing,he,pairFst_pair,pairSnd_pair,fraction_coefficients_code]
  · rw [hd]
    exact fraction_coefficients_rational_values ps hp

theorem rational_list_parser_result_shape (input : List Bool) (b : Bool)
    (fractions : List (List Bool)) (tail : List Bool)
    (h : encodedRationalListParser input=pair [b] (pair (payloadListCode fractions) tail)) :
    rationalListParserResult input=
      if b then some ((fractions.map fractionWordValue).reverse,tail) else none := by
  have hd := decode_fraction_payloads_code (payloadListCode fractions).length fractions (le_refl _)
  cases b <;> simp [rationalListParserResult,h,hd]

/-- On every successful paper decode, the concrete output contains exact integral scalings,
    the same unused tail and one strictly positive common denominator. -/
theorem rational_list_clearing_correct (input : List Bool) (values : List ℚ) (tail : List Bool)
    (h : readRationals (wordValue (pairFst input)) (pairSnd input)=some (values,tail)) :
    ∃ denominator coefficients,
      encodedRationalListClearing input=pair [true]
        (pair denominator (pair (payloadListCode coefficients) tail)) ∧
      0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        values.map (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=values.length := by
  obtain ⟨b,ps,rest,he,hp,ho,hv⟩ := rational_list_clearing_payload_shape input
  have hr := rational_list_parser_result_shape input b ps rest he
  rw [rational_list_parser_exact,h] at hr
  cases b with
  | false => simp at hr
  | true =>
    have heq : values=(ps.map fractionWordValue).reverse ∧ tail=rest := by simpa using hr
    obtain ⟨rfl,rfl⟩ := heq
    refine ⟨polynomialRationalListDenominator input,(coefficientWords [true] ps).reverse,
      ho,rational_list_denominator_positive input,hv,?_⟩
    simp only [List.length_reverse,List.length_map,coefficient_words_length]

theorem rational_list_clearing_actual_codes (values : List ℚ) (tail : List Bool) :
    ∃ denominator coefficients,
      encodedRationalListClearing (pair values.length.bits (values.flatMap IV04.Paper.rationalCode ++ tail))=
        pair [true] (pair denominator (pair (payloadListCode coefficients) tail)) ∧
      0 < wordValue denominator ∧
      coefficients.map (fun w => (signedWordValue w : ℚ))=
        values.map (fun q => q*(wordValue denominator : ℚ)) ∧
      coefficients.length=values.length := by
  apply rational_list_clearing_correct
  simp only [pairFst_pair,pairSnd_pair,word_value_foldr,IV04.Paper.bits_foldr]
  exact read_rationals_codes values tail

theorem rational_list_clearing_failure (input : List Bool)
    (h : readRationals (wordValue (pairFst input)) (pairSnd input)=none) :
    pairFst (encodedRationalListClearing input)=[false] := by
  obtain ⟨b,ps,rest,he,hp,ho,hv⟩ := rational_list_clearing_payload_shape input
  have hr := rational_list_parser_result_shape input b ps rest he
  rw [rational_list_parser_exact,h] at hr
  cases b with
  | false => rw [ho,pairFst_pair]
  | true => simp at hr

theorem rational_list_clearing_actual_polytime : encodedRationalListClearing ∈ FP ∧
    ∀ input values tail,
      readRationals (wordValue (pairFst input)) (pairSnd input)=some (values,tail) →
      ∃ denominator coefficients,
        encodedRationalListClearing input=pair [true]
          (pair denominator (pair (payloadListCode coefficients) tail)) ∧
        0 < wordValue denominator ∧
        coefficients.map (fun w => (signedWordValue w : ℚ))=
          values.map (fun q => q*(wordValue denominator : ℚ)) ∧
        coefficients.length=values.length :=
  ⟨encoded_rational_list_clearing_mem_fp,rational_list_clearing_correct⟩

#print axioms rational_list_clearing_actual_polytime
end IV04.Paper.Computational
