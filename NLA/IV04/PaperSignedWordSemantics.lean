module

public import NLA.IV04.PaperSignedWordDefinitions
public import NLA.IV04.PaperWordSubtractionSemantics
public import NLA.IV04.PaperWordMultiplierPoly
public import NLA.IV04.PaperCanonicalWord
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem signed_word_pack_value (flag magnitude : List Bool) :
    signedWordValue (signedWordPack flag magnitude)=
      if firstBit flag then -(wordValue magnitude : ℤ) else (wordValue magnitude : ℤ) := by
  cases flag with
  | nil => simp [signedWordPack,Complexity.caseBit₀,signedWordValue,firstBit,canonical_word_value]
  | cons b flag =>
    cases b <;> simp [signedWordPack,Complexity.caseBit₀,signedWordValue,firstBit,canonical_word_value]

theorem signed_word_pack_flag_value (b : Bool) (magnitude : List Bool) :
    signedWordValue (signedWordPack [b] magnitude)=
      if b then -(wordValue magnitude : ℤ) else (wordValue magnitude : ℤ) := by
  simpa [firstBit] using signed_word_pack_value [b] magnitude

theorem polynomial_signed_neg_value (bits : List Bool) :
    signedWordValue (polynomialSignedNeg bits)=-signedWordValue bits := by
  simp only [polynomialSignedNeg,head_flag]
  generalize h : firstBit bits=b
  cases b <;> simp [Complexity.notBit,Complexity.caseBit₀,signed_word_pack_flag_value] <;>
    simp [signedWordValue,h]

theorem polynomial_signed_multiply_value (left right : List Bool) :
    signedWordValue (polynomialSignedMultiply left right)=signedWordValue left*signedWordValue right := by
  simp only [polynomialSignedMultiply,head_flag]
  generalize ha : firstBit left=a
  generalize hb : firstBit right=b
  cases a <;> cases b <;>
    simp [xorFlag,Complexity.caseBit₀,Complexity.notBit,signed_word_pack_flag_value,
      polynomial_word_multiply_value] <;> simp [signedWordValue,ha,hb]

theorem polynomial_signed_add_value (left right : List Bool) :
    signedWordValue (polynomialSignedAdd left right)=signedWordValue left+signedWordValue right := by
  simp only [polynomialSignedAdd,head_flag,polynomial_word_le_value]
  by_cases h : wordValue left.tail ≤ wordValue right.tail
  · generalize ha : firstBit left=a
    generalize hb : firstBit right=b
    cases a <;> cases b <;>
      simp [h,xorFlag,Complexity.caseBit₀,Complexity.notBit,signed_word_pack_flag_value,
        polynomial_word_sub_value,polynomial_word_add_value] <;>
      simp [signedWordValue,ha,hb,Int.ofNat_sub h] <;> omega
  · have hr : wordValue right.tail ≤ wordValue left.tail := by omega
    generalize ha : firstBit left=a
    generalize hb : firstBit right=b
    cases a <;> cases b <;>
      simp [h,xorFlag,Complexity.caseBit₀,Complexity.notBit,signed_word_pack_flag_value,
        polynomial_word_sub_value,polynomial_word_add_value] <;>
      simp [signedWordValue,ha,hb,Int.ofNat_sub hr] <;> omega

theorem signed_word_pack_length (flag magnitude : List Bool) :
    (signedWordPack flag magnitude).length ≤ magnitude.length+1 := by
  have h := canonical_word_length magnitude
  cases flag with
  | nil => simp [signedWordPack,Complexity.caseBit₀]; omega
  | cons b flag => cases b <;> simp [signedWordPack,Complexity.caseBit₀] <;> omega

#print axioms polynomial_signed_add_value
end IV04.Paper.Computational
