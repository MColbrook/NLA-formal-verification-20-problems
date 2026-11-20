module

public import NLA.IV04.PaperPayloadReversePoly
public import NLA.IV04.PaperRationalListParserComplete
public import NLA.IV04.PaperWordListPositive
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem payload_reverse_iterate_nil (k : ℕ) (output : List Bool) :
    (payloadReverseStep^[k]) (pair [] output)=pair [] output := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,payload_reverse_step_pair]; simp

theorem payload_reverse_iterate_code (k : ℕ) (payloads output : List (List Bool))
    (h : payloads.length ≤ k) :
    (payloadReverseStep^[k]) (pair (payloadListCode payloads) (payloadListCode output))=
      pair [] (payloadListCode (payloads.reverse ++ output)) := by
  induction k generalizing payloads output with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,payload_reverse_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h; omega
      rw [Function.iterate_succ_apply,payload_reverse_step_pair]
      simp only [payloadListCode,payload_pair_ne_nil,if_false,pairFst_pair,pairSnd_pair]
      have hi := ih payloads (payload :: output) ht
      simp only [payloadListCode] at hi
      rw [hi]
      simp [List.reverse_cons,List.append_assoc]

theorem payload_reverse_code (payloads : List (List Bool)) :
    polynomialPayloadReverse (payloadListCode payloads)=
      payloadListCode (payloads.reverse) := by
  have h := payload_reverse_iterate_code (payloadListCode payloads).length payloads []
    (payload_list_count_length payloads)
  simpa only [polynomialPayloadReverse,payloadReverseState,payloadListCode,
    pairSnd_pair,List.append_nil] using congrArg pairSnd h

theorem payload_reverse_involution_code (payloads : List (List Bool)) :
    polynomialPayloadReverse (polynomialPayloadReverse (payloadListCode payloads))=
      payloadListCode payloads := by
  rw [payload_reverse_code,payload_reverse_code,List.reverse_reverse]

theorem payload_reverse_actual_polytime : polynomialPayloadReverse ∈ FP ∧
    (∀ input, (polynomialPayloadReverse input).length ≤ 4*input.length+2) ∧
    (∀ payloads, polynomialPayloadReverse (payloadListCode payloads)=
      payloadListCode payloads.reverse) :=
  ⟨polynomial_payload_reverse_mem_fp,payload_reverse_output_length,payload_reverse_code⟩

#print axioms payload_reverse_actual_polytime
end IV04.Paper.Computational
