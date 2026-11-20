module

public import NLA.IV04.PaperPayloadCountPoly
public import NLA.IV04.PaperWordListProductSemantics
public import NLA.IV04.PaperWordAdderSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

 theorem payload_count_iterate_nil (k : ℕ) (count : List Bool) :
    (payloadCountStep^[k]) (pair [] count)=pair [] count := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,payload_count_step_pair];simp

 theorem payload_count_iteration_value (k : ℕ) (payloads : List (List Bool)) (count : List Bool)
    (h : payloads.length ≤ k) :
    wordValue (pairSnd ((payloadCountStep^[k]) (pair (payloadListCode payloads) count)))=
      wordValue count+payloads.length := by
  induction k generalizing payloads count with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,payload_count_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h;omega
      rw [Function.iterate_succ_apply,payload_count_step_pair]
      have hn : pair payload (payloadListCode payloads)≠[] := by
        intro he
        have hl := congrArg List.length he
        simp only [pair_length,List.length_nil] at hl
        omega
      simp only [payloadListCode,hn,if_false,pairSnd_pair]
      rw [ih payloads (polynomialWordAdd count [true]) ht,polynomial_word_add_value]
      simp [wordValue,bitValue] <;> omega

 theorem polynomial_payload_count_value (payloads : List (List Bool)) :
    wordValue (polynomialPayloadCount (payloadListCode payloads))=payloads.length := by
  have h := payload_count_iteration_value (payloadListCode payloads).length payloads []
    (payload_list_count_length payloads)
  simpa [polynomialPayloadCount,canonical_word_value,payloadCountState,wordValue] using h

 theorem polynomial_payload_count_exact (payloads : List (List Bool)) :
    polynomialPayloadCount (payloadListCode payloads)=payloads.length.bits := by
  have h := payload_count_iteration_value (payloadListCode payloads).length payloads []
    (payload_list_count_length payloads)
  simp only [wordValue,Nat.zero_add] at h
  simp only [polynomialPayloadCount,canonical_word_eq_bits]
  rw [show wordValue (pairSnd (payloadCountState (payloadListCode payloads)))=payloads.length from h]

 theorem payload_count_actual_polytime : polynomialPayloadCount ∈ FP ∧
    (∀ input, (polynomialPayloadCount input).length ≤ 4*input.length+2) ∧
    (∀ payloads, polynomialPayloadCount (payloadListCode payloads)=payloads.length.bits) :=
  ⟨polynomial_payload_count_mem_fp,polynomial_payload_count_length,polynomial_payload_count_exact⟩

#print axioms polynomial_payload_count_exact
#print axioms payload_count_actual_polytime
end IV04.Paper.Computational
