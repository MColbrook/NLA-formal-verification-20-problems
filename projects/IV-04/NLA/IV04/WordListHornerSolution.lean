module

public import NLA.IV04.PaperWordListHornerInput
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace IV04.Paper.Computational
open Complexity SATReduction
theorem verified_word_list_horner_clock_length : ∀ (clock input : List Bool),
  ((wordListHornerStep^[clock.length])
      (Complexity.pair (Complexity.pairSnd input) (Complexity.pair (Complexity.pairFst input) []))).length ≤
        4*input.length+4+clock.length*(input.length+1) := word_list_horner_clock_length

theorem verified_polynomial_word_list_horner_mem_fp : polynomialWordListHorner ∈ FP := polynomial_word_list_horner_mem_fp

theorem verified_polynomial_word_list_horner_value : ∀ (payloads : List (List Bool)) (base : List Bool),
  wordValue (polynomialWordListHorner (Complexity.pair base (payloadListCode payloads))) =
      payloads.foldl (fun value coefficient => value*wordValue base+wordValue coefficient) 0 := polynomial_word_list_horner_value

theorem verified_word_list_horner_actual_polytime : polynomialWordListHorner ∈ Complexity.FP ∧
    ∀ (payloads : List (List Bool)) (base : List Bool),
      wordValue (polynomialWordListHorner (Complexity.pair base (payloadListCode payloads))) =
        payloads.foldl (fun value coefficient => value*wordValue base+wordValue coefficient) 0 := word_list_horner_actual_polytime

theorem verified_polynomial_word_list_horner_positional_value : ∀ (b n : ℕ) (d : Fin n → ℕ),
  wordValue (polynomialWordListHorner (encodedPositionalDigits b n d))=positionalValue b d := polynomial_word_list_horner_positional_value

theorem verified_word_list_horner_positional_actual_polytime : polynomialWordListHorner ∈ Complexity.FP ∧
    ∀ (b n : ℕ) (d : Fin n → ℕ),
      wordValue (polynomialWordListHorner (encodedPositionalDigits b n d))=positionalValue b d := word_list_horner_positional_actual_polytime

theorem verified_actual_sat_weight_horner_word_value : ∀ (φ : Complexity.SAT.CNF) (i : SATSlot φ),
  wordValue (polynomialWordListHorner (actualSATWeightHornerInput φ i))=satSubsetWeights φ i := actual_sat_weight_horner_word_value

theorem verified_actual_sat_target_horner_word_value : ∀ (φ : Complexity.SAT.CNF),
  wordValue (polynomialWordListHorner (actualSATTargetHornerInput φ))=satSubsetTarget φ := actual_sat_target_horner_word_value

#print axioms IV04.Paper.Computational.verified_word_list_horner_clock_length
#print axioms IV04.Paper.Computational.verified_polynomial_word_list_horner_mem_fp
#print axioms IV04.Paper.Computational.verified_polynomial_word_list_horner_value
#print axioms IV04.Paper.Computational.verified_word_list_horner_actual_polytime
#print axioms IV04.Paper.Computational.verified_polynomial_word_list_horner_positional_value
#print axioms IV04.Paper.Computational.verified_word_list_horner_positional_actual_polytime
#print axioms IV04.Paper.Computational.verified_actual_sat_weight_horner_word_value
#print axioms IV04.Paper.Computational.verified_actual_sat_target_horner_word_value
end IV04.Paper.Computational
end
