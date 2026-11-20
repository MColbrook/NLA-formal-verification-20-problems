module

public import NLA.IV04.PaperFractionCoefficientPoly
public import NLA.IV04.PaperFractionCoefficientReference
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem fraction_coefficient_iterate_nil (k : ℕ) (prior output : List Bool) :
    (fractionCoefficientStep^[k]) (coefficientPack [] prior output)=coefficientPack [] prior output := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,fraction_coefficient_step_pack]; simp

theorem fraction_coefficient_iterate_code (k : ℕ) (prior : List Bool)
    (fractions output : List (List Bool)) (h : fractions.length ≤ k) :
    (fractionCoefficientStep^[k]) (coefficientPack (payloadListCode fractions) prior (payloadListCode output))=
      coefficientPack [] (coefficientFinalPrior prior fractions)
        (payloadListCode ((coefficientWords prior fractions).reverse ++ output)) := by
  induction k generalizing prior fractions output with
  | zero =>
    have he : fractions=[] := by cases fractions <;> simp_all
    simp [he,payloadListCode,coefficientWords,coefficientFinalPrior]
  | succ k ih =>
    cases fractions with
    | nil => simp [payloadListCode,coefficientWords,coefficientFinalPrior,fraction_coefficient_iterate_nil]
    | cons fraction fractions =>
      have ht : fractions.length ≤ k := by simp only [List.length_cons] at h; omega
      rw [Function.iterate_succ_apply,fraction_coefficient_step_pack]
      simp only [payloadListCode,payload_pair_ne_nil,if_false,pairFst_pair,pairSnd_pair]
      have hi := ih (canonicalWordMultiply prior (pairSnd fraction)) fractions
        (clearedFractionWord prior fraction (payloadListCode fractions) :: output) ht
      simp only [payloadListCode] at hi
      rw [hi]
      simp [coefficientWords,coefficientFinalPrior,List.reverse_cons,List.append_assoc]

theorem fraction_coefficients_code (fractions : List (List Bool)) :
    polynomialFractionCoefficients (payloadListCode fractions)=
      payloadListCode ((coefficientWords [true] fractions).reverse) := by
  have h := fraction_coefficient_iterate_code (payloadListCode fractions).length [true] fractions []
    (payload_list_count_length fractions)
  simpa only [polynomialFractionCoefficients,fractionCoefficientState,fractionCoefficientInitial,
    coefficientOutput,coefficientPack,pairSnd_pair,List.append_nil,payloadListCode]
    using congrArg coefficientOutput h

theorem coefficient_words_length (prior : List Bool) (fractions : List (List Bool)) :
    (coefficientWords prior fractions).length=fractions.length := by
  induction fractions generalizing prior with
  | nil => rfl
  | cons fraction fractions ih => simp [coefficientWords,ih]

theorem coefficient_final_prior_value (prior : List Bool) (fractions : List (List Bool)) :
    wordValue (coefficientFinalPrior prior fractions)=wordValue prior*fractionDenominatorProduct fractions := by
  induction fractions generalizing prior with
  | nil => simp [coefficientFinalPrior,fractionDenominatorProduct]
  | cons fraction fractions ih =>
    simp [coefficientFinalPrior,ih,canonical_word_multiply_value,fractionDenominatorProduct,mul_assoc]

theorem coefficient_words_rational_values (prior : List Bool) (fractions : List (List Bool))
    (hp : ∀ w ∈ fractions, 0 < wordValue (pairSnd w)) :
    (coefficientWords prior fractions).map (fun w => (signedWordValue w : ℚ))=
      fractions.map (fun w => fractionWordValue w * ((wordValue prior*fractionDenominatorProduct fractions : ℕ) : ℚ)) := by
  induction fractions generalizing prior with
  | nil => simp [coefficientWords]
  | cons fraction fractions ih =>
    have hd : 0 < wordValue (pairSnd fraction) := hp fraction (by simp)
    have ht : ∀ w ∈ fractions, 0 < wordValue (pairSnd w) := fun w hw => hp w (by simp [hw])
    have hn : (wordValue (pairSnd fraction) : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    simp only [coefficientWords,List.map_cons,cleared_fraction_word_value,Int.cast_mul,Int.cast_natCast]
    rw [ih _ ht]
    apply congrArg₂ List.cons
    · simp only [fractionWordValue,fractionDenominatorProduct,List.map_cons,List.prod_cons,Nat.cast_mul]
      field_simp [hn]
    · simp only [canonical_word_multiply_value,fractionDenominatorProduct,List.map_cons,List.prod_cons]
      congr 1
      funext w
      congr 2
      ring

#print axioms coefficient_words_rational_values
end IV04.Paper.Computational
