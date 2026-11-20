module

public import NLA.IV04.PaperScaledThresholdDefinitions
public import NLA.IV04.PaperSignedOrderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem encoded_scaled_determinant_threshold_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedScaledDeterminantThreshold (v 0) := by
  have hE := Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))
  have hT := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  have hD := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))
  have hP := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))))
  have hl := Cobham.comp₂ Cobham.pairing hT hD
  have hr := Cobham.comp₂ Cobham.pairing hE hP
  exact (Cobham.comp₂ polynomial_fraction_le_cobham hl hr).of_eq fun _ => rfl

theorem encoded_scaled_determinant_threshold_mem_fp : encodedScaledDeterminantThreshold ∈ FP :=
  CobhamFP_subset_FP encoded_scaled_determinant_threshold_cobham

theorem scaled_determinant_threshold_word_values (determinant threshold denominator power : List Bool) :
    encodedScaledDeterminantThreshold (pair determinant (pair threshold (pair denominator power)))=
      [decide ((signedWordValue threshold : ℚ)/(wordValue denominator : ℚ) ≤
        (signedWordValue determinant : ℚ)/(wordValue power : ℚ))] := by
  simpa only [encodedScaledDeterminantThreshold,pairFst_pair,pairSnd_pair,fractionWordValue] using
    polynomial_fraction_le_value (pair threshold denominator) (pair determinant power)

theorem scaled_determinant_threshold_correct (determinant threshold denominator power : List Bool)
    (n : ℕ) (value cutoff : ℚ) (hD : 0 < wordValue denominator)
    (hP : wordValue power=wordValue denominator ^ n)
    (hE : (signedWordValue determinant : ℚ)/(wordValue denominator : ℚ)^n=value)
    (hT : (signedWordValue threshold : ℚ)=cutoff*(wordValue denominator : ℚ)) :
    encodedScaledDeterminantThreshold (pair determinant (pair threshold (pair denominator power)))=
      [decide (cutoff ≤ value)] := by
  have hd : (0 : ℚ) < wordValue denominator := by exact_mod_cast hD
  have hl : (signedWordValue threshold : ℚ)/(wordValue denominator : ℚ)=cutoff := by
    rw [hT]
    exact mul_div_cancel_right₀ cutoff (ne_of_gt hd)
  have hr : (signedWordValue determinant : ℚ)/(wordValue power : ℚ)=value := by
    rw [hP,Nat.cast_pow]
    exact hE
  rw [scaled_determinant_threshold_word_values,hl,hr]

theorem scaled_determinant_threshold_actual_polytime : encodedScaledDeterminantThreshold ∈ FP ∧
    ∀ determinant threshold denominator power,
      encodedScaledDeterminantThreshold (pair determinant (pair threshold (pair denominator power)))=
        [decide ((signedWordValue threshold : ℚ)/(wordValue denominator : ℚ) ≤
          (signedWordValue determinant : ℚ)/(wordValue power : ℚ))] :=
  ⟨encoded_scaled_determinant_threshold_mem_fp,scaled_determinant_threshold_word_values⟩

#print axioms scaled_determinant_threshold_correct
#print axioms scaled_determinant_threshold_actual_polytime
end IV04.Paper.Computational
