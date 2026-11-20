module

public import NLA.IV04.PaperSignedWordBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_bit_value_le_one (b : Bool) : bitValue b ≤ 1 := by
  exact bit_value_le_one b

theorem verified_word_value_lt_pow_length (bits : List Bool) : wordValue bits < 2^bits.length := by
  exact word_value_lt_pow_length bits

theorem verified_word_value_append (left right : List Bool) :
    wordValue (left++right)=wordValue left+2^left.length*wordValue right := by
  exact word_value_append left right

theorem verified_word_value_zeros (k : ℕ) : wordValue (List.replicate k false)=0 := by
  exact word_value_zeros k

theorem verified_word_value_pad (ruler bits : List Bool) (h : bits.length ≤ ruler.length) :
    wordValue (Complexity.padTo ruler bits)=wordValue bits := by
  exact word_value_pad ruler bits h

theorem verified_word_value_complement (bits : List Bool) :
    wordValue (bits.map Bool.not)+wordValue bits+1=2^bits.length := by
  exact word_value_complement bits

theorem verified_word_value_split (bits : List Bool) (k : ℕ) :
    wordValue bits=wordValue (bits.take k)+2^k*wordValue (bits.drop k) := by
  exact word_value_split bits k

theorem verified_word_value_take_bound (bits : List Bool) (k : ℕ) :
    wordValue (bits.take k) < 2^k := by
  exact word_value_take_bound bits k

theorem verified_word_value_take_mod (bits : List Bool) (k : ℕ) :
    wordValue (bits.take k)=wordValue bits % 2^k := by
  exact word_value_take_mod bits k

theorem verified_raw_word_difference_value (left right : List Bool)
    (h : wordValue right ≤ wordValue left) :
    wordValue (rawWordDifference left right)=wordValue left-wordValue right := by
  exact raw_word_difference_value left right h

theorem verified_polynomial_word_sub_value (left right : List Bool) :
    wordValue (polynomialWordSub left right)=wordValue left-wordValue right := by
  exact polynomial_word_sub_value left right

theorem verified_raw_word_difference_length (left right : List Bool) :
    (rawWordDifference left right).length ≤ left.length+right.length+1 := by
  exact raw_word_difference_length left right

theorem verified_polynomial_word_sub_length (left right : List Bool) :
    (polynomialWordSub left right).length ≤ left.length+right.length+1 := by
  exact polynomial_word_sub_length left right

theorem verified_word_complement_cobham :
    Cobham fun v : Fin 1 → List Bool => (v 0).map Bool.not := by
  exact word_complement_cobham

theorem verified_raw_word_difference_cobham :
    Cobham fun v : Fin 2 → List Bool => rawWordDifference (v 0) (v 1) := by
  exact raw_word_difference_cobham

theorem verified_polynomial_word_sub_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialWordSub (v 0) (v 1) := by
  exact polynomial_word_sub_cobham

theorem verified_encoded_word_sub_mem_fp : encodedPolynomialWordSub ∈ FP := by
  exact encoded_word_sub_mem_fp

theorem verified_encoded_word_sub_actual_polytime : encodedPolynomialWordSub ∈ FP ∧
    ∀ left right, wordValue (encodedPolynomialWordSub (Complexity.pair left right))=
      wordValue left-wordValue right := by
  exact encoded_word_sub_actual_polytime

theorem verified_signed_word_pack_value (flag magnitude : List Bool) :
    signedWordValue (signedWordPack flag magnitude)=
      if firstBit flag then -(wordValue magnitude : ℤ) else (wordValue magnitude : ℤ) := by
  exact signed_word_pack_value flag magnitude

theorem verified_signed_word_pack_flag_value (b : Bool) (magnitude : List Bool) :
    signedWordValue (signedWordPack [b] magnitude)=
      if b then -(wordValue magnitude : ℤ) else (wordValue magnitude : ℤ) := by
  exact signed_word_pack_flag_value b magnitude

theorem verified_polynomial_signed_neg_value (bits : List Bool) :
    signedWordValue (polynomialSignedNeg bits)=-signedWordValue bits := by
  exact polynomial_signed_neg_value bits

theorem verified_polynomial_signed_multiply_value (left right : List Bool) :
    signedWordValue (polynomialSignedMultiply left right)=signedWordValue left*signedWordValue right := by
  exact polynomial_signed_multiply_value left right

theorem verified_polynomial_signed_add_value (left right : List Bool) :
    signedWordValue (polynomialSignedAdd left right)=signedWordValue left+signedWordValue right := by
  exact polynomial_signed_add_value left right

theorem verified_signed_word_pack_length (flag magnitude : List Bool) :
    (signedWordPack flag magnitude).length ≤ magnitude.length+1 := by
  exact signed_word_pack_length flag magnitude

theorem verified_signed_word_pack_cobham {n : ℕ}
    {flag magnitude : (Fin n → List Bool) → List Bool}
    (hf : Cobham flag) (hm : Cobham magnitude) :
    Cobham fun v => signedWordPack (flag v) (magnitude v) := by
  exact signed_word_pack_cobham hf hm

theorem verified_polynomial_signed_neg_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSignedNeg (v 0) := by
  exact polynomial_signed_neg_cobham

theorem verified_polynomial_signed_add_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialSignedAdd (v 0) (v 1) := by
  exact polynomial_signed_add_cobham

theorem verified_polynomial_signed_multiply_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialSignedMultiply (v 0) (v 1) := by
  exact polynomial_signed_multiply_cobham

theorem verified_signed_neg_mem_fp : polynomialSignedNeg ∈ FP := by
  exact signed_neg_mem_fp

theorem verified_encoded_signed_add_mem_fp : encodedPolynomialSignedAdd ∈ FP := by
  exact encoded_signed_add_mem_fp

theorem verified_encoded_signed_multiply_mem_fp : encodedPolynomialSignedMultiply ∈ FP := by
  exact encoded_signed_multiply_mem_fp

theorem verified_signed_neg_actual_polytime : polynomialSignedNeg ∈ FP ∧
    ∀ bits, signedWordValue (polynomialSignedNeg bits)=-signedWordValue bits := by
  exact signed_neg_actual_polytime

theorem verified_encoded_signed_add_actual_polytime : encodedPolynomialSignedAdd ∈ FP ∧
    ∀ left right, signedWordValue (encodedPolynomialSignedAdd (Complexity.pair left right))=
      signedWordValue left+signedWordValue right := by
  exact encoded_signed_add_actual_polytime

theorem verified_encoded_signed_multiply_actual_polytime : encodedPolynomialSignedMultiply ∈ FP ∧
    ∀ left right, signedWordValue (encodedPolynomialSignedMultiply (Complexity.pair left right))=
      signedWordValue left*signedWordValue right := by
  exact encoded_signed_multiply_actual_polytime

theorem verified_case_bit_zero_property {P : List Bool → Prop} (flag left right : List Bool)
    (hl : P left) (hr : P right) : P (Complexity.caseBit₀ flag left right) := by
  exact case_bit_zero_property flag left right hl hr

theorem verified_signed_word_abs_value (bits : List Bool) :
    (signedWordValue bits).natAbs=wordValue bits.tail := by
  exact signed_word_abs_value bits

theorem verified_signed_word_pack_tail (flag magnitude : List Bool) :
    (signedWordPack flag magnitude).tail=canonicalWord magnitude := by
  exact signed_word_pack_tail flag magnitude

theorem verified_signed_word_pack_canonical (flag magnitude : List Bool) :
    (signedWordPack flag magnitude).tail=(signedWordValue (signedWordPack flag magnitude)).natAbs.bits := by
  exact signed_word_pack_canonical flag magnitude

theorem verified_polynomial_signed_neg_canonical (bits : List Bool) :
    (polynomialSignedNeg bits).tail=(signedWordValue (polynomialSignedNeg bits)).natAbs.bits := by
  exact polynomial_signed_neg_canonical bits

theorem verified_polynomial_signed_multiply_canonical (left right : List Bool) :
    (polynomialSignedMultiply left right).tail=
      (signedWordValue (polynomialSignedMultiply left right)).natAbs.bits := by
  exact polynomial_signed_multiply_canonical left right

theorem verified_polynomial_signed_add_canonical (left right : List Bool) :
    (polynomialSignedAdd left right).tail=(signedWordValue (polynomialSignedAdd left right)).natAbs.bits := by
  exact polynomial_signed_add_canonical left right

theorem verified_polynomial_signed_add_length (left right : List Bool) :
    (polynomialSignedAdd left right).length ≤ left.tail.length+right.tail.length+2 := by
  exact polynomial_signed_add_length left right

theorem verified_polynomial_signed_multiply_length (left right : List Bool) :
    (polynomialSignedMultiply left right).length ≤ left.tail.length*(right.tail.length+2)+1 := by
  exact polynomial_signed_multiply_length left right

#print axioms IV04.Paper.Computational.verified_bit_value_le_one
#print axioms IV04.Paper.Computational.verified_word_value_lt_pow_length
#print axioms IV04.Paper.Computational.verified_word_value_append
#print axioms IV04.Paper.Computational.verified_word_value_zeros
#print axioms IV04.Paper.Computational.verified_word_value_pad
#print axioms IV04.Paper.Computational.verified_word_value_complement
#print axioms IV04.Paper.Computational.verified_word_value_split
#print axioms IV04.Paper.Computational.verified_word_value_take_bound
#print axioms IV04.Paper.Computational.verified_word_value_take_mod
#print axioms IV04.Paper.Computational.verified_raw_word_difference_value
#print axioms IV04.Paper.Computational.verified_polynomial_word_sub_value
#print axioms IV04.Paper.Computational.verified_raw_word_difference_length
#print axioms IV04.Paper.Computational.verified_polynomial_word_sub_length
#print axioms IV04.Paper.Computational.verified_word_complement_cobham
#print axioms IV04.Paper.Computational.verified_raw_word_difference_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_word_sub_cobham
#print axioms IV04.Paper.Computational.verified_encoded_word_sub_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_word_sub_actual_polytime
#print axioms IV04.Paper.Computational.verified_signed_word_pack_value
#print axioms IV04.Paper.Computational.verified_signed_word_pack_flag_value
#print axioms IV04.Paper.Computational.verified_polynomial_signed_neg_value
#print axioms IV04.Paper.Computational.verified_polynomial_signed_multiply_value
#print axioms IV04.Paper.Computational.verified_polynomial_signed_add_value
#print axioms IV04.Paper.Computational.verified_signed_word_pack_length
#print axioms IV04.Paper.Computational.verified_signed_word_pack_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_signed_neg_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_signed_add_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_signed_multiply_cobham
#print axioms IV04.Paper.Computational.verified_signed_neg_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_signed_add_mem_fp
#print axioms IV04.Paper.Computational.verified_encoded_signed_multiply_mem_fp
#print axioms IV04.Paper.Computational.verified_signed_neg_actual_polytime
#print axioms IV04.Paper.Computational.verified_encoded_signed_add_actual_polytime
#print axioms IV04.Paper.Computational.verified_encoded_signed_multiply_actual_polytime
#print axioms IV04.Paper.Computational.verified_case_bit_zero_property
#print axioms IV04.Paper.Computational.verified_signed_word_abs_value
#print axioms IV04.Paper.Computational.verified_signed_word_pack_tail
#print axioms IV04.Paper.Computational.verified_signed_word_pack_canonical
#print axioms IV04.Paper.Computational.verified_polynomial_signed_neg_canonical
#print axioms IV04.Paper.Computational.verified_polynomial_signed_multiply_canonical
#print axioms IV04.Paper.Computational.verified_polynomial_signed_add_canonical
#print axioms IV04.Paper.Computational.verified_polynomial_signed_add_length
#print axioms IV04.Paper.Computational.verified_polynomial_signed_multiply_length
end IV04.Paper.Computational
