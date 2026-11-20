module

public import NLA.IV04.PaperSignedOrderPoly
public import NLA.IV04.PaperLengthWord
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_canonical_nonempty_flag (bits : List Bool) :
    Complexity.nonemptyFlag (canonicalWord bits)=if wordValue bits=0 then [] else [true] := by
  exact canonical_nonempty_flag bits

theorem verified_signed_negative_flag_bits (bits : List Bool) :
    signedNegativeFlag bits=[if firstBit bits then decide (wordValue bits.tail ≠ 0) else false] := by
  exact signed_negative_flag_bits bits

theorem verified_signed_negative_flag (bits : List Bool) :
    signedNegativeFlag bits=[decide (signedWordValue bits < 0)] := by
  exact signed_negative_flag bits

theorem verified_polynomial_signed_le_value (left right : List Bool) :
    polynomialSignedLe left right=[decide (signedWordValue left ≤ signedWordValue right)] := by
  exact polynomial_signed_le_value left right

theorem verified_polynomial_fraction_le_value (left right : List Bool) :
    polynomialFractionLe left right=[decide (fractionWordValue left ≤ fractionWordValue right)] := by
  exact polynomial_fraction_le_value left right

theorem verified_signed_negative_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => signedNegativeFlag (v 0) := by
  exact signed_negative_flag_cobham

theorem verified_polynomial_signed_le_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialSignedLe (v 0) (v 1) := by
  exact polynomial_signed_le_cobham

theorem verified_polynomial_fraction_le_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialFractionLe (v 0) (v 1) := by
  exact polynomial_fraction_le_cobham

theorem verified_encoded_signed_le_mem_fp : encodedPolynomialSignedLe ∈ FP := by
  exact encoded_signed_le_mem_fp

theorem verified_encoded_fraction_le_mem_fp : encodedPolynomialFractionLe ∈ FP := by
  exact encoded_fraction_le_mem_fp

theorem verified_encoded_signed_le_actual_polytime : encodedPolynomialSignedLe ∈ FP ∧
    ∀ left right, encodedPolynomialSignedLe (pair left right)=
      [decide (signedWordValue left ≤ signedWordValue right)] := by
  exact encoded_signed_le_actual_polytime

theorem verified_encoded_fraction_le_actual_polytime : encodedPolynomialFractionLe ∈ FP ∧
    ∀ left right, encodedPolynomialFractionLe (pair left right)=
      [decide (fractionWordValue left ≤ fractionWordValue right)] := by
  exact encoded_fraction_le_actual_polytime

theorem verified_raw_length_word_value (input : List Bool) : wordValue (rawLengthWord input)=input.length := by
  exact raw_length_word_value input

theorem verified_raw_length_word_length (input : List Bool) : (rawLengthWord input).length ≤ 2*input.length := by
  exact raw_length_word_length input

theorem verified_input_length_word_value (input : List Bool) : wordValue (inputLengthWord input)=input.length := by
  exact input_length_word_value input

theorem verified_input_length_word_exact (input : List Bool) : inputLengthWord input=input.length.bits := by
  exact input_length_word_exact input

theorem verified_raw_length_word_cobham :
    Cobham fun v : Fin 1 → List Bool => rawLengthWord (v 0) := by
  exact raw_length_word_cobham

theorem verified_input_length_word_cobham :
    Cobham fun v : Fin 1 → List Bool => inputLengthWord (v 0) := by
  exact input_length_word_cobham

theorem verified_input_length_word_mem_fp : inputLengthWord ∈ FP := by
  exact input_length_word_mem_fp

theorem verified_input_length_actual_polytime : inputLengthWord ∈ FP ∧
    ∀ input, inputLengthWord input=input.length.bits := by
  exact input_length_actual_polytime

#print axioms IV04.Paper.Computational.verified_canonical_nonempty_flag
#print axioms IV04.Paper.Computational.verified_signed_negative_flag_bits
#print axioms IV04.Paper.Computational.verified_signed_negative_flag
#print axioms IV04.Paper.Computational.verified_polynomial_signed_le_value
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_le_value
#print axioms IV04.Paper.Computational.verified_signed_negative_flag_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_signed_le_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_fraction_le_cobham
#print axioms IV04.Paper.Computational.verified_encoded_signed_le_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_fraction_le_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_signed_le_actual_polytime
#print axioms IV04.Paper.Computational.verified_encoded_fraction_le_actual_polytime
#print axioms IV04.Paper.Computational.verified_raw_length_word_value
#print axioms IV04.Paper.Computational.verified_raw_length_word_length
#print axioms IV04.Paper.Computational.verified_input_length_word_value
#print axioms IV04.Paper.Computational.verified_input_length_word_exact
#print axioms IV04.Paper.Computational.verified_raw_length_word_cobham
#print axioms IV04.Paper.Computational.verified_input_length_word_cobham
#print axioms IV04.Paper.Computational.verified_input_length_word_mem_fp
#print axioms IV04.Paper.Computational.verified_input_length_actual_polytime
end IV04.Paper.Computational
