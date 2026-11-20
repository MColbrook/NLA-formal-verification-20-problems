module

public import NLA.IV04.PaperScaledThreshold
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_encoded_scaled_determinant_threshold_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedScaledDeterminantThreshold (v 0) := by
  exact encoded_scaled_determinant_threshold_cobham

theorem verified_encoded_scaled_determinant_threshold_mem_fp : encodedScaledDeterminantThreshold ∈ FP := by
  exact encoded_scaled_determinant_threshold_mem_fp

theorem verified_scaled_determinant_threshold_word_values (determinant threshold denominator power : List Bool) :
    encodedScaledDeterminantThreshold (pair determinant (pair threshold (pair denominator power)))=
      [decide ((signedWordValue threshold : ℚ)/(wordValue denominator : ℚ) ≤
        (signedWordValue determinant : ℚ)/(wordValue power : ℚ))] := by
  exact scaled_determinant_threshold_word_values determinant threshold denominator power

theorem verified_scaled_determinant_threshold_correct (determinant threshold denominator power : List Bool)
    (n : ℕ) (value cutoff : ℚ) (hD : 0 < wordValue denominator)
    (hP : wordValue power=wordValue denominator ^ n)
    (hE : (signedWordValue determinant : ℚ)/(wordValue denominator : ℚ)^n=value)
    (hT : (signedWordValue threshold : ℚ)=cutoff*(wordValue denominator : ℚ)) :
    encodedScaledDeterminantThreshold (pair determinant (pair threshold (pair denominator power)))=
      [decide (cutoff ≤ value)] := by
  exact scaled_determinant_threshold_correct determinant threshold denominator power n value cutoff hD hP hE hT

theorem verified_scaled_determinant_threshold_actual_polytime : encodedScaledDeterminantThreshold ∈ FP ∧
    ∀ determinant threshold denominator power,
      encodedScaledDeterminantThreshold (pair determinant (pair threshold (pair denominator power)))=
        [decide ((signedWordValue threshold : ℚ)/(wordValue denominator : ℚ) ≤
          (signedWordValue determinant : ℚ)/(wordValue power : ℚ))] := by
  exact scaled_determinant_threshold_actual_polytime

#print axioms IV04.Paper.Computational.verified_encoded_scaled_determinant_threshold_cobham
#print axioms IV04.Paper.Computational.verified_encoded_scaled_determinant_threshold_mem_fp
#print axioms IV04.Paper.Computational.verified_scaled_determinant_threshold_word_values
#print axioms IV04.Paper.Computational.verified_scaled_determinant_threshold_correct
#print axioms IV04.Paper.Computational.verified_scaled_determinant_threshold_actual_polytime
end IV04.Paper.Computational
