module

public import NLA.IV04.PaperPayloadWordMaxPoly
public import NLA.IV04.PaperWordListProductSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

 theorem polynomial_word_max_value (left right : List Bool) :
    wordValue (polynomialWordMax left right)=max (wordValue left) (wordValue right) := by
  by_cases h : wordValue left ≤ wordValue right
  · simp [polynomialWordMax,polynomial_word_le_value,h,caseBit₀,caseBit,max_eq_right h]
  · have hl : wordValue right ≤ wordValue left := by omega
    simp [polynomialWordMax,polynomial_word_le_value,h,caseBit₀,caseBit,max_eq_left hl]

 theorem payload_word_max_iterate_nil (select : List Bool → List Bool) (k : ℕ) (maximum : List Bool) :
    ((payloadWordMaxStep select)^[k]) (pair [] maximum)=pair [] maximum := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,payload_word_max_step_pair];simp

 theorem payload_word_max_iteration_value (select : List Bool → List Bool) (k : ℕ)
    (payloads : List (List Bool)) (maximum : List Bool) (h : payloads.length ≤ k) :
    wordValue (pairSnd (((payloadWordMaxStep select)^[k]) (pair (payloadListCode payloads) maximum)))=
      max (wordValue maximum) ((payloads.map fun p => wordValue (select p)).foldr max 0) := by
  induction k generalizing payloads maximum with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,payload_word_max_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h;omega
      rw [Function.iterate_succ_apply,payload_word_max_step_pair]
      have hn : pair payload (payloadListCode payloads)≠[] := by
        intro he
        have hl := congrArg List.length he
        simp only [pair_length,List.length_nil] at hl
        omega
      simp only [payloadListCode,hn,if_false,pairSnd_pair,pairFst_pair]
      rw [ih payloads (polynomialWordMax maximum (select payload)) ht,polynomial_word_max_value]
      simp only [List.map_cons,List.foldr_cons,max_assoc]

 theorem polynomial_payload_word_max_exact (select : List Bool → List Bool)
    (payloads : List (List Bool)) :
    polynomialPayloadWordMax select (payloadListCode payloads)=
      ((payloads.map fun p => wordValue (select p)).foldr max 0).bits := by
  have h := payload_word_max_iteration_value select (payloadListCode payloads).length payloads []
    (payload_list_count_length payloads)
  simp only [wordValue,Nat.zero_max] at h
  simp only [polynomialPayloadWordMax,canonical_word_eq_bits]
  rw [show wordValue (pairSnd (payloadWordMaxState select (payloadListCode payloads)))=
    (payloads.map fun p => wordValue (select p)).foldr max 0 from h]

end IV04.Paper.Computational
