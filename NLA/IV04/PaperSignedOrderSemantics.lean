module

public import NLA.IV04.PaperSignedOrderDefinitions
public import NLA.IV04.PaperFractionWordSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem canonical_nonempty_flag (bits : List Bool) :
    Complexity.nonemptyFlag (canonicalWord bits)=if wordValue bits=0 then [] else [true] := by
  cases h : canonicalWord bits with
  | nil =>
    have hz := (canonical_word_eq_nil bits).mp h
    simp [Complexity.nonemptyFlag,Complexity.caseBit,hz]
  | cons b tail =>
    have hz : wordValue bits ≠ 0 := by
      intro hz
      have he := (canonical_word_eq_nil bits).mpr hz
      rw [h] at he
      contradiction
    simp [Complexity.nonemptyFlag,Complexity.caseBit,hz]

theorem signed_negative_flag_bits (bits : List Bool) :
    signedNegativeFlag bits=[if firstBit bits then decide (wordValue bits.tail ≠ 0) else false] := by
  simp only [signedNegativeFlag,head_flag,canonical_nonempty_flag]
  cases h : firstBit bits <;>
    by_cases hz : wordValue bits.tail=0 <;>
    simp [Complexity.andBit,Complexity.caseBit₀,h,hz]

theorem signed_negative_flag (bits : List Bool) :
    signedNegativeFlag bits=[decide (signedWordValue bits < 0)] := by
  rw [signed_negative_flag_bits]
  cases h : firstBit bits <;> simp [signedWordValue,h,Nat.pos_iff_ne_zero]

theorem polynomial_signed_le_value (left right : List Bool) :
    polynomialSignedLe left right=[decide (signedWordValue left ≤ signedWordValue right)] := by
  simp only [polynomialSignedLe,signed_negative_flag_bits,polynomial_word_le_value]
  cases ha : firstBit left <;> cases hb : firstBit right <;>
    by_cases hl : wordValue left.tail=0 <;> by_cases hr : wordValue right.tail=0 <;>
    simp [signedWordValue,ha,hb,hl,hr,xorFlag,Complexity.caseBit₀,Complexity.notBit] <;> omega

theorem polynomial_fraction_le_value (left right : List Bool) :
    polynomialFractionLe left right=[decide (fractionWordValue left ≤ fractionWordValue right)] := by
  have hl : (0 : ℚ) < wordValue (Complexity.pairSnd (normalizeFractionWord left)) := by
    exact_mod_cast normalize_fraction_denominator_positive left
  have hr : (0 : ℚ) < wordValue (Complexity.pairSnd (normalizeFractionWord right)) := by
    exact_mod_cast normalize_fraction_denominator_positive right
  simp only [polynomialFractionLe,polynomial_signed_le_value,polynomial_signed_multiply_value,
    positive_signed_word_value]
  congr 2
  rw [←normalize_fraction_word_value left,←normalize_fraction_word_value right]
  unfold fractionWordValue
  rw [div_le_div_iff₀ hl hr]
  apply propext
  exact_mod_cast (Iff.rfl :
    signedWordValue (Complexity.pairFst (normalizeFractionWord left)) *
      (wordValue (Complexity.pairSnd (normalizeFractionWord right)) : ℤ) ≤
    signedWordValue (Complexity.pairFst (normalizeFractionWord right)) *
      (wordValue (Complexity.pairSnd (normalizeFractionWord left)) : ℤ) ↔ _)

#print axioms polynomial_fraction_le_value
end IV04.Paper.Computational
