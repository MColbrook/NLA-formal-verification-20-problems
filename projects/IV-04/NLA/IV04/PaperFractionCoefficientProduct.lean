module

public import NLA.IV04.PaperFractionCoefficientDefinitions
public import NLA.IV04.PaperFractionListDenominatorsSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem fraction_word_list_denominator_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionWordListDenominator (v 0) := by
  have hp : Cobham fun v : Fin 1 → List Bool => polynomialWordListProduct (v 0) :=
    (Cobham.sndBlockFn word_list_product_state_cobham).of_eq fun _ => rfl
  have hprod := Cobham.comp hp fun _ : Fin 1 => polynomial_fraction_list_denominators_cobham
  exact (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hprod).of_eq fun _ => rfl

theorem fraction_word_list_denominator_mem_fp : fractionWordListDenominator ∈ FP :=
  CobhamFP_subset_FP fraction_word_list_denominator_cobham

theorem fraction_word_list_denominator_value (payloads : List (List Bool)) :
    wordValue (fractionWordListDenominator (payloadListCode payloads))=
      ((payloads.map pairSnd).map wordValue).prod := by
  simp only [fractionWordListDenominator,canonical_word_value,fraction_list_denominators_code,
    polynomial_word_list_product_value,List.map_reverse,List.prod_reverse]

theorem fraction_word_list_denominator_length (input : List Bool) :
    (fractionWordListDenominator input).length ≤ 8*input.length+7 := by
  have hd := fraction_list_denominators_output_length input
  have hp := polynomial_word_list_product_length (polynomialFractionListDenominators input)
  have hc := canonical_word_length (polynomialWordListProduct (polynomialFractionListDenominators input))
  change (canonicalWord (polynomialWordListProduct (polynomialFractionListDenominators input))).length ≤ _
  omega

#print axioms fraction_word_list_denominator_mem_fp
end IV04.Paper.Computational
