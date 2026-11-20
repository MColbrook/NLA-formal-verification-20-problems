module

public import NLA.IV04.PaperFractionWordDefinitions
public import NLA.IV04.PaperSignedWordBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem canonical_word_eq_nil (bits : List Bool) : canonicalWord bits=[] ↔ wordValue bits=0 := by
  constructor
  · intro h
    have hv := canonical_word_value bits
    rw [h] at hv
    exact hv.symm
  · intro h
    simp [canonical_word_eq_bits,h]

theorem normalize_fraction_word_cases (input : List Bool) :
    normalizeFractionWord input=
      if wordValue (Complexity.pairSnd input)=0 then Complexity.pair [false] [true]
      else Complexity.pair (Complexity.pairFst input) (canonicalWord (Complexity.pairSnd input)) := by
  cases hd : canonicalWord (Complexity.pairSnd input) with
  | nil =>
    have hz := (canonical_word_eq_nil _).mp hd
    simp [normalizeFractionWord,hd,hz,Complexity.nonemptyFlag,Complexity.caseBit,Complexity.caseBit₀]
  | cons b bits =>
    have hz : wordValue (Complexity.pairSnd input) ≠ 0 := by
      intro h
      have he := (canonical_word_eq_nil _).mpr h
      rw [hd] at he
      contradiction
    simp [normalizeFractionWord,hd,hz,Complexity.nonemptyFlag,Complexity.caseBit,Complexity.caseBit₀]

theorem normalize_fraction_denominator_positive (input : List Bool) :
    0 < wordValue (Complexity.pairSnd (normalizeFractionWord input)) := by
  rw [normalize_fraction_word_cases]
  split_ifs with h
  · simp [wordValue,bitValue]
  · simp only [Complexity.pairSnd_pair,canonical_word_value]
    omega

theorem normalize_fraction_word_value (input : List Bool) :
    fractionWordValue (normalizeFractionWord input)=fractionWordValue input := by
  rw [normalize_fraction_word_cases]
  split_ifs with h
  · simp [fractionWordValue,h,signedWordValue,firstBit,wordValue,bitValue]
  · simp [fractionWordValue,canonical_word_value]

theorem positive_signed_word_value (bits : List Bool) :
    signedWordValue (false :: bits)=(wordValue bits : ℤ) := by
  simp [signedWordValue,firstBit]

theorem polynomial_fraction_add_value (left right : List Bool) :
    fractionWordValue (polynomialFractionAdd left right)=fractionWordValue left+fractionWordValue right := by
  have hl : (wordValue (Complexity.pairSnd (normalizeFractionWord left)) : ℚ) ≠ 0 := by
    exact_mod_cast (normalize_fraction_denominator_positive left).ne'
  have hr : (wordValue (Complexity.pairSnd (normalizeFractionWord right)) : ℚ) ≠ 0 := by
    exact_mod_cast (normalize_fraction_denominator_positive right).ne'
  rw [←normalize_fraction_word_value left,←normalize_fraction_word_value right]
  simp only [polynomialFractionAdd,fractionWordValue,Complexity.pairFst_pair,Complexity.pairSnd_pair,
    polynomial_signed_add_value,polynomial_signed_multiply_value,positive_signed_word_value,
    polynomial_word_multiply_value,Int.cast_add,Int.cast_mul,Int.cast_natCast,Nat.cast_mul]
  field_simp [hl,hr]
  <;> ring

theorem polynomial_fraction_multiply_value (left right : List Bool) :
    fractionWordValue (polynomialFractionMultiply left right)=fractionWordValue left*fractionWordValue right := by
  rw [←normalize_fraction_word_value left,←normalize_fraction_word_value right]
  simp only [polynomialFractionMultiply,fractionWordValue,Complexity.pairFst_pair,Complexity.pairSnd_pair,
    polynomial_signed_multiply_value,polynomial_word_multiply_value,Int.cast_mul,Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

theorem polynomial_fraction_add_denominator_positive (left right : List Bool) :
    0 < wordValue (Complexity.pairSnd (polynomialFractionAdd left right)) := by
  simp only [polynomialFractionAdd,Complexity.pairSnd_pair,polynomial_word_multiply_value]
  exact Nat.mul_pos (normalize_fraction_denominator_positive left)
    (normalize_fraction_denominator_positive right)

theorem polynomial_fraction_multiply_denominator_positive (left right : List Bool) :
    0 < wordValue (Complexity.pairSnd (polynomialFractionMultiply left right)) := by
  simp only [polynomialFractionMultiply,Complexity.pairSnd_pair,polynomial_word_multiply_value]
  exact Nat.mul_pos (normalize_fraction_denominator_positive left)
    (normalize_fraction_denominator_positive right)

#print axioms polynomial_fraction_add_value
end IV04.Paper.Computational
