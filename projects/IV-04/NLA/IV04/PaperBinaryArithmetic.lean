module

public import NLA.IV04.PaperBinaryArithmeticDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem full_adder_identity (a b carry : Bool) :
    bitValue (sumBit a b carry)+2*bitValue (carryBit a b carry)=
      bitValue a+bitValue b+bitValue carry := by
  cases a <;> cases b <;> cases carry <;>
    norm_num [bitValue,sumBit,carryBit]

theorem increment_word_value (bits : List Bool) (carry : Bool) :
    wordValue (incrementWord carry bits)=wordValue bits+bitValue carry := by
  induction bits generalizing carry with
  | nil => cases carry <;> simp [incrementWord,wordValue,bitValue]
  | cons b bits ih =>
    cases carry <;> cases b <;> simp [incrementWord,wordValue,bitValue,ih] <;> omega

theorem increment_word_length (bits : List Bool) (carry : Bool) :
    (incrementWord carry bits).length ≤ bits.length+1 := by
  induction bits generalizing carry with
  | nil => cases carry <;> simp [incrementWord]
  | cons b bits ih =>
    cases carry <;> cases b <;> simp [incrementWord] <;> exact ih true

theorem add_words_value (left right : List Bool) (carry : Bool) :
    wordValue (addWords carry left right)=wordValue left+wordValue right+bitValue carry := by
  induction left generalizing right carry with
  | nil => simp [addWords,wordValue,increment_word_value]
  | cons a left ih =>
    cases right with
    | nil => simp [addWords,wordValue,increment_word_value]
    | cons b right =>
      simp only [addWords,wordValue,ih]
      have h := full_adder_identity a b carry
      omega

theorem add_words_length (left right : List Bool) (carry : Bool) :
    (addWords carry left right).length ≤ left.length+right.length+1 := by
  induction left generalizing right carry with
  | nil => simpa [addWords] using increment_word_length right carry
  | cons a left ih =>
    cases right with
    | nil => simpa [addWords] using increment_word_length (a::left) carry
    | cons b right =>
      simp only [addWords,List.length_cons]
      have h := ih right (carryBit a b carry)
      omega

theorem word_value_foldr (bits : List Bool) : wordValue bits=bits.foldr Nat.bit 0 := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    cases b <;> simp [wordValue,bitValue,List.foldr_cons,ih,Nat.bit_val] <;> omega

theorem multiply_words_value (left right : List Bool) :
    wordValue (multiplyWords left right)=wordValue left*wordValue right := by
  induction left with
  | nil => simp [multiplyWords,wordValue]
  | cons b left ih =>
    cases b <;> simp [multiplyWords,add_words_value,wordValue,bitValue,ih] <;> ring

theorem multiply_words_length (left right : List Bool) :
    (multiplyWords left right).length ≤ left.length*(right.length+2) := by
  induction left with
  | nil => simp [multiplyWords]
  | cons b left ih =>
    have h := add_words_length (if b then right else []) (false :: multiplyWords left right) false
    have hb : (if b then right else []).length ≤ right.length := by cases b <;> simp
    simp only [multiplyWords,List.length_cons] at h ⊢
    nlinarith

#print axioms add_words_value
end IV04.Paper.Computational
