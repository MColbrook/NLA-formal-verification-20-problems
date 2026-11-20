module

public import NLA.IV04.PaperFractionListDenominatorsSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_fraction_list_denominators_step_pair (rest output : List Bool) :
    fractionListDenominatorsStep (Complexity.pair rest output)=
      if rest=[] then Complexity.pair rest output else Complexity.pair (Complexity.pairSnd rest)
        (Complexity.pair (Complexity.pairSnd (Complexity.pairFst rest)) output) := by
  exact fraction_list_denominators_step_pair rest output

theorem verified_fraction_list_denominators_step_shape (rest output : List Bool) :
    ∃ r o : List Bool, fractionListDenominatorsStep (Complexity.pair rest output)=Complexity.pair r o ∧
      (Complexity.pair r o).length ≤ (Complexity.pair rest output).length+2 := by
  exact fraction_list_denominators_step_shape rest output

theorem verified_fraction_list_denominators_iterate_shape (k : ℕ) (rest output : List Bool) :
    ∃ r o : List Bool, (fractionListDenominatorsStep^[k]) (Complexity.pair rest output)=Complexity.pair r o ∧
      (Complexity.pair r o).length ≤ (Complexity.pair rest output).length+2*k := by
  exact fraction_list_denominators_iterate_shape k rest output

theorem verified_fraction_list_denominators_iterate_length (k : ℕ) (rest output : List Bool) :
    ((fractionListDenominatorsStep^[k]) (Complexity.pair rest output)).length ≤
      2*rest.length+output.length+2+2*k := by
  exact fraction_list_denominators_iterate_length k rest output

theorem verified_fraction_list_denominators_output_length (input : List Bool) :
    (polynomialFractionListDenominators input).length ≤ 4*input.length+2 := by
  exact fraction_list_denominators_output_length input

theorem verified_fraction_list_denominators_step_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionListDenominatorsStep (v 0) := by
  exact fraction_list_denominators_step_cobham

theorem verified_fraction_list_denominators_state_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionListDenominatorsState (v 0) := by
  exact fraction_list_denominators_state_cobham

theorem verified_polynomial_fraction_list_denominators_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialFractionListDenominators (v 0) := by
  exact polynomial_fraction_list_denominators_cobham

theorem verified_polynomial_fraction_list_denominators_mem_fp : polynomialFractionListDenominators ∈ FP := by
  exact polynomial_fraction_list_denominators_mem_fp

theorem verified_rational_list_denominator_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialRationalListDenominator (v 0) := by
  exact rational_list_denominator_cobham

theorem verified_rational_list_denominator_mem_fp : polynomialRationalListDenominator ∈ FP := by
  exact rational_list_denominator_mem_fp

theorem verified_fraction_list_denominators_iterate_nil (k : ℕ) (output : List Bool) :
    (fractionListDenominatorsStep^[k]) (pair [] output)=pair [] output := by
  exact fraction_list_denominators_iterate_nil k output

theorem verified_fraction_list_denominators_iterate_code (k : ℕ) (payloads output : List (List Bool))
    (h : payloads.length ≤ k) :
    (fractionListDenominatorsStep^[k]) (pair (payloadListCode payloads) (payloadListCode output))=
      pair [] (payloadListCode ((payloads.map pairSnd).reverse ++ output)) := by
  exact fraction_list_denominators_iterate_code k payloads output h

theorem verified_fraction_list_denominators_code (payloads : List (List Bool)) :
    polynomialFractionListDenominators (payloadListCode payloads)=
      payloadListCode ((payloads.map pairSnd).reverse) := by
  exact fraction_list_denominators_code payloads

theorem verified_rational_list_denominator_value (input : List Bool) :
    ∃ b ps rest, encodedRationalListParser input=pair [b] (pair (payloadListCode ps) rest) ∧
      (∀ w ∈ ps, 0 < wordValue (pairSnd w)) ∧
      wordValue (polynomialRationalListDenominator input)=((ps.map pairSnd).map wordValue).prod := by
  exact rational_list_denominator_value input

theorem verified_rational_list_denominator_positive (input : List Bool) :
    0 < wordValue (polynomialRationalListDenominator input) := by
  exact rational_list_denominator_positive input

theorem verified_counted_output_length_le (state : List Bool) : (countedOutput state).length ≤ state.length := by
  exact counted_output_length_le state

theorem verified_polynomial_word_list_product_length (input : List Bool) :
    (polynomialWordListProduct input).length ≤ 2*input.length+3 := by
  exact polynomial_word_list_product_length input

theorem verified_rational_list_denominator_length (input : List Bool) :
    (polynomialRationalListDenominator input).length ≤
      8*(2*input.length+8+input.length*(4*input.length+12))+7 := by
  exact rational_list_denominator_length input

theorem verified_rational_list_denominator_actual_polytime : polynomialRationalListDenominator ∈ FP ∧
    ∀ input, 0 < wordValue (polynomialRationalListDenominator input) ∧
      (polynomialRationalListDenominator input).length ≤
        8*(2*input.length+8+input.length*(4*input.length+12))+7 := by
  exact rational_list_denominator_actual_polytime

#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_step_pair
#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_step_shape
#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_iterate_shape
#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_iterate_length
#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_output_length
#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_step_cobham
#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_state_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_list_denominators_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_list_denominators_mem_fp
#print axioms IV04.Paper.Computational.verified_rational_list_denominator_cobham
#print axioms IV04.Paper.Computational.verified_rational_list_denominator_mem_fp
#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_iterate_nil
#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_iterate_code
#print axioms IV04.Paper.Computational.verified_fraction_list_denominators_code
#print axioms IV04.Paper.Computational.verified_rational_list_denominator_value
#print axioms IV04.Paper.Computational.verified_rational_list_denominator_positive
#print axioms IV04.Paper.Computational.verified_counted_output_length_le
#print axioms IV04.Paper.Computational.verified_polynomial_word_list_product_length
#print axioms IV04.Paper.Computational.verified_rational_list_denominator_length
#print axioms IV04.Paper.Computational.verified_rational_list_denominator_actual_polytime
end IV04.Paper.Computational
