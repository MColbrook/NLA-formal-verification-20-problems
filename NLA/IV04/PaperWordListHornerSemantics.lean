module

public import NLA.IV04.PaperWordListHornerPoly
public import NLA.IV04.PaperWordListSumSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem word_list_horner_iterate_nil (k : ℕ) (base total : List Bool) :
    (wordListHornerStep^[k]) (Complexity.pair [] (Complexity.pair base total)) =
      Complexity.pair [] (Complexity.pair base total) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,word_list_horner_step_pair]; simp

theorem word_list_horner_iteration_value (k : ℕ) (payloads : List (List Bool))
    (base total : List Bool) (h : payloads.length ≤ k) :
    wordValue (Complexity.pairSnd (Complexity.pairSnd ((wordListHornerStep^[k])
      (Complexity.pair (payloadListCode payloads) (Complexity.pair base total))))) =
        payloads.foldl (fun value coefficient => value*wordValue base+wordValue coefficient) (wordValue total) := by
  induction k generalizing payloads total with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,word_list_horner_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h; omega
      rw [Function.iterate_succ_apply,word_list_horner_step_pair]
      simp only [payloadListCode,payload_pair_ne_nil,if_false,Complexity.pairFst_pair,Complexity.pairSnd_pair]
      rw [ih payloads (polynomialWordAdd (canonicalWordMultiply total base) payload) ht,
        polynomial_word_add_value,canonical_word_multiply_value,List.foldl_cons]

theorem polynomial_word_list_horner_value (payloads : List (List Bool)) (base : List Bool) :
    wordValue (polynomialWordListHorner (Complexity.pair base (payloadListCode payloads))) =
      payloads.foldl (fun value coefficient => value*wordValue base+wordValue coefficient) 0 := by
  have hp := payload_list_count_length payloads
  have hc : payloads.length ≤ (Complexity.pair base (payloadListCode payloads)).length := by
    rw [Complexity.pair_length]
    omega
  have h := word_list_horner_iteration_value (Complexity.pair base (payloadListCode payloads)).length
    payloads base [] hc
  simpa only [polynomialWordListHorner,wordListHornerState,Complexity.pairFst_pair,
    Complexity.pairSnd_pair,wordValue] using h

theorem word_list_horner_actual_polytime : polynomialWordListHorner ∈ Complexity.FP ∧
    ∀ (payloads : List (List Bool)) (base : List Bool),
      wordValue (polynomialWordListHorner (Complexity.pair base (payloadListCode payloads))) =
        payloads.foldl (fun value coefficient => value*wordValue base+wordValue coefficient) 0 :=
  ⟨polynomial_word_list_horner_mem_fp,polynomial_word_list_horner_value⟩

#print axioms word_list_horner_actual_polytime
end IV04.Paper.Computational
