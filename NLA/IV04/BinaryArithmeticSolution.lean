module

public import NLA.IV04.PaperIncrementPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem verified_full_adder_identity (a b carry : Bool) :
    bitValue (sumBit a b carry)+2*bitValue (carryBit a b carry)=
      bitValue a+bitValue b+bitValue carry := by
  exact full_adder_identity a b carry

theorem verified_increment_word_value (bits : List Bool) (carry : Bool) :
    wordValue (incrementWord carry bits)=wordValue bits+bitValue carry := by
  exact increment_word_value bits carry

theorem verified_increment_word_length (bits : List Bool) (carry : Bool) :
    (incrementWord carry bits).length ≤ bits.length+1 := by
  exact increment_word_length bits carry

theorem verified_add_words_value (left right : List Bool) (carry : Bool) :
    wordValue (addWords carry left right)=wordValue left+wordValue right+bitValue carry := by
  exact add_words_value left right carry

theorem verified_add_words_length (left right : List Bool) (carry : Bool) :
    (addWords carry left right).length ≤ left.length+right.length+1 := by
  exact add_words_length left right carry

theorem verified_word_value_foldr (bits : List Bool) : wordValue bits=bits.foldr Nat.bit 0 := by
  exact word_value_foldr bits

theorem verified_multiply_words_value (left right : List Bool) :
    wordValue (multiplyWords left right)=wordValue left*wordValue right := by
  exact multiply_words_value left right

theorem verified_multiply_words_length (left right : List Bool) :
    (multiplyWords left right).length ≤ left.length*(right.length+2) := by
  exact multiply_words_length left right

theorem verified_increment_word_cobham :
    Complexity.Cobham fun v : Fin 1 → List Bool => incrementWord true (v 0) := by
  exact increment_word_cobham

theorem verified_increment_word_mem_fp :
    (fun bits : List Bool => incrementWord true bits) ∈ Complexity.FP := by
  exact increment_word_mem_fp

theorem verified_increment_word_actual_polytime :
    (fun bits : List Bool => incrementWord true bits) ∈ Complexity.FP ∧
      ∀ bits, wordValue (incrementWord true bits)=wordValue bits+1 ∧
        (incrementWord true bits).length ≤ bits.length+1 := by
  exact increment_word_actual_polytime

#print axioms IV04.Paper.Computational.verified_full_adder_identity
#print axioms IV04.Paper.Computational.verified_increment_word_value
#print axioms IV04.Paper.Computational.verified_increment_word_length
#print axioms IV04.Paper.Computational.verified_add_words_value
#print axioms IV04.Paper.Computational.verified_add_words_length
#print axioms IV04.Paper.Computational.verified_word_value_foldr
#print axioms IV04.Paper.Computational.verified_multiply_words_value
#print axioms IV04.Paper.Computational.verified_multiply_words_length
#print axioms IV04.Paper.Computational.verified_increment_word_cobham
#print axioms IV04.Paper.Computational.verified_increment_word_mem_fp
#print axioms IV04.Paper.Computational.verified_increment_word_actual_polytime
end IV04.Paper.Computational
