module

public import NLA.IV04.PaperSignedWordPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem case_bit_zero_property {P : List Bool → Prop} (flag left right : List Bool)
    (hl : P left) (hr : P right) : P (Complexity.caseBit₀ flag left right) := by
  cases flag with
  | nil => exact hr
  | cons b bits => cases b <;> assumption

theorem signed_word_abs_value (bits : List Bool) :
    (signedWordValue bits).natAbs=wordValue bits.tail := by
  unfold signedWordValue
  split_ifs <;> simp

theorem signed_word_pack_tail (flag magnitude : List Bool) :
    (signedWordPack flag magnitude).tail=canonicalWord magnitude := by
  cases flag with
  | nil => rfl
  | cons b bits => cases b <;> rfl

theorem signed_word_pack_canonical (flag magnitude : List Bool) :
    (signedWordPack flag magnitude).tail=(signedWordValue (signedWordPack flag magnitude)).natAbs.bits := by
  rw [signed_word_abs_value,signed_word_pack_tail,canonical_word_value]
  exact canonical_word_eq_bits magnitude

theorem polynomial_signed_neg_canonical (bits : List Bool) :
    (polynomialSignedNeg bits).tail=(signedWordValue (polynomialSignedNeg bits)).natAbs.bits := by
  unfold polynomialSignedNeg
  exact signed_word_pack_canonical _ _

theorem polynomial_signed_multiply_canonical (left right : List Bool) :
    (polynomialSignedMultiply left right).tail=
      (signedWordValue (polynomialSignedMultiply left right)).natAbs.bits := by
  unfold polynomialSignedMultiply
  exact signed_word_pack_canonical _ _

theorem polynomial_signed_add_canonical (left right : List Bool) :
    (polynomialSignedAdd left right).tail=(signedWordValue (polynomialSignedAdd left right)).natAbs.bits := by
  unfold polynomialSignedAdd
  apply case_bit_zero_property (P:=fun bits => bits.tail=(signedWordValue bits).natAbs.bits)
  · apply case_bit_zero_property (P:=fun bits => bits.tail=(signedWordValue bits).natAbs.bits) <;>
      exact signed_word_pack_canonical _ _
  · exact signed_word_pack_canonical _ _

theorem polynomial_signed_add_length (left right : List Bool) :
    (polynomialSignedAdd left right).length ≤ left.tail.length+right.tail.length+2 := by
  unfold polynomialSignedAdd
  apply case_bit_zero_property (P:=fun bits => bits.length ≤ left.tail.length+right.tail.length+2)
  · apply case_bit_zero_property (P:=fun bits => bits.length ≤ left.tail.length+right.tail.length+2)
    · have hp := signed_word_pack_length (Complexity.bitAt [] right) (polynomialWordSub right.tail left.tail)
      have hs := polynomial_word_sub_length right.tail left.tail
      omega
    · have hp := signed_word_pack_length (Complexity.bitAt [] left) (polynomialWordSub left.tail right.tail)
      have hs := polynomial_word_sub_length left.tail right.tail
      omega
  · have hp := signed_word_pack_length (Complexity.bitAt [] left) (polynomialWordAdd left.tail right.tail)
    have hs := polynomial_word_add_length left.tail right.tail
    omega

theorem polynomial_signed_multiply_length (left right : List Bool) :
    (polynomialSignedMultiply left right).length ≤ left.tail.length*(right.tail.length+2)+1 := by
  unfold polynomialSignedMultiply
  have hp := signed_word_pack_length
    (xorFlag (Complexity.bitAt [] left) (Complexity.bitAt [] right))
    (polynomialWordMultiply left.tail right.tail)
  have hm := polynomial_word_multiply_length left.tail right.tail
  omega

#print axioms polynomial_signed_add_canonical
end IV04.Paper.Computational
