module

public import NLA.IV04.PaperCanonicalProduct
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem signed_word_pack_nonempty (flag magnitude : List Bool) :
    signedWordPack flag magnitude ≠ [] := by
  cases flag with
  | nil => simp [signedWordPack]
  | cons b bits => cases b <;> simp [signedWordPack]

theorem polynomial_signed_add_nonempty (left right : List Bool) :
    polynomialSignedAdd left right ≠ [] := by
  unfold polynomialSignedAdd
  apply case_bit_zero_property (P:=fun bits => bits ≠ [])
  · apply case_bit_zero_property (P:=fun bits => bits ≠ []) <;> exact signed_word_pack_nonempty _ _
  · exact signed_word_pack_nonempty _ _

theorem canonical_signed_word_length (bits : List Bool)
    (hc : bits.tail=(signedWordValue bits).natAbs.bits) (hne : bits ≠ []) :
    bits.length=(signedWordValue bits).natAbs.size+1 := by
  rw [←Nat.size_eq_bits_len,←hc]
  cases bits with
  | nil => exact (hne rfl).elim
  | cons b bs => rfl

theorem signed_add_magnitude_size (left right : List Bool) :
    (signedWordValue left+signedWordValue right).natAbs.size ≤
      max left.tail.length right.tail.length+1 := by
  let m := max left.tail.length right.tail.length
  have hl := word_value_lt_pow_length left.tail
  have hr := word_value_lt_pow_length right.tail
  have hpl : (2 : ℕ)^left.tail.length ≤ 2^m := Nat.pow_le_pow_right (by omega) (Nat.le_max_left _ _)
  have hpr : (2 : ℕ)^right.tail.length ≤ 2^m := Nat.pow_le_pow_right (by omega) (Nat.le_max_right _ _)
  have ha := Int.natAbs_add_le (signedWordValue left) (signedWordValue right)
  rw [signed_word_abs_value,signed_word_abs_value] at ha
  apply Nat.size_le.mpr
  change (signedWordValue left+signedWordValue right).natAbs < 2^(m+1)
  rw [pow_succ]
  omega

theorem polynomial_signed_add_max_length (left right : List Bool) :
    (polynomialSignedAdd left right).length ≤ max left.tail.length right.tail.length+2 := by
  rw [canonical_signed_word_length _ (polynomial_signed_add_canonical left right)
    (polynomial_signed_add_nonempty left right),polynomial_signed_add_value]
  have h := signed_add_magnitude_size left right
  omega

theorem polynomial_signed_neg_tail_length (bits : List Bool) :
    (polynomialSignedNeg bits).tail.length ≤ bits.tail.length := by
  rw [polynomialSignedNeg,signed_word_pack_tail]
  exact canonical_word_length bits.tail

#print axioms polynomial_signed_add_max_length
end IV04.Paper.Computational
