module

public import NLA.IV04.PaperBoundedPayloadRepeatPoly
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
private theorem bounded_repeat_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr];exact IV04.Paper.bits_foldr n
 theorem bounded_payload_repeat_step_nat (i bound : ℕ) (coefficient output : List Bool) :
    boundedPayloadRepeatStep (variableMarkerPack i.bits bound.bits coefficient output)=
      if i<bound then variableMarkerPack (i+1).bits bound.bits coefficient (pair coefficient output)
      else variableMarkerPack i.bits bound.bits coefficient output := by
  rw [bounded_payload_repeat_step_pair,polynomial_word_le_value]
  simp only [bounded_repeat_bits_value]
  by_cases h : i<bound
  · simp [h,Nat.not_le_of_gt h,notBit,caseBit₀,canonical_word_eq_bits,
      polynomial_word_add_value,bounded_repeat_bits_value,wordValue,bitValue]
  · simp [h,Nat.le_of_not_gt h,notBit,caseBit₀]
 theorem bounded_payload_repeat_iterate_inactive (k i bound : ℕ) (coefficient output : List Bool)
    (h : bound ≤ i) :
    (boundedPayloadRepeatStep^[k]) (variableMarkerPack i.bits bound.bits coefficient output)=
      variableMarkerPack i.bits bound.bits coefficient output := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,bounded_payload_repeat_step_nat];simp [Nat.not_lt.mpr h]
private theorem bounded_repeat_append_cons (n : ℕ) (word : List Bool) (output : List (List Bool)) :
    List.replicate n word ++ word::output=word::(List.replicate n word++output) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append,List.cons.injEq,true_and] using ih
 theorem bounded_payload_repeat_iteration_code (k i bound : ℕ) (coefficient : List Bool)
    (output : List (List Bool)) (hi : i ≤ bound) (hclock : bound-i ≤ k) :
    (boundedPayloadRepeatStep^[k]) (variableMarkerPack i.bits bound.bits coefficient (payloadListCode output))=
      variableMarkerPack bound.bits bound.bits coefficient
        (payloadListCode (List.replicate (bound-i) coefficient ++ output)) := by
  induction k generalizing i output with
  | zero =>
    have he : i=bound := by omega
    subst i
    simp
  | succ k ih =>
    by_cases he : i=bound
    · subst i
      rw [bounded_payload_repeat_iterate_inactive (k+1) bound bound coefficient _ (le_refl _)]
      simp
    · have hil : i<bound := by omega
      have hc : bound-(i+1) ≤ k := by omega
      have hs : bound-i=(bound-(i+1))+1 := by omega
      rw [Function.iterate_succ_apply,bounded_payload_repeat_step_nat]
      simp only [hil,if_true]
      have ht := ih (i+1) (coefficient::output) (by omega) hc
      simp only [payloadListCode] at ht
      rw [ht,hs,List.replicate_succ,bounded_repeat_append_cons]
      rfl
 theorem polynomial_bounded_payload_repeat_exact (ruler coefficient : List Bool) (bound : ℕ)
    (h : bound ≤ ruler.length+1) :
    polynomialBoundedPayloadRepeat (pair ruler (pair bound.bits coefficient))=
      payloadListCode (List.replicate bound coefficient) := by
  have hi := bounded_payload_repeat_iteration_code (ruler.length+1) 0 bound coefficient [] (Nat.zero_le _) (by simpa using h)
  have hz : (0 : ℕ).bits=[] := rfl
  simpa only [polynomialBoundedPayloadRepeat,boundedPayloadRepeatState,pairFst_pair,pairSnd_pair,
    variableMarkerPack,payloadListCode,hz,Nat.sub_zero,List.append_nil]
      using congrArg (fun s => pairSnd (pairSnd (pairSnd s))) hi
 theorem bounded_payload_repeat_actual_polytime : polynomialBoundedPayloadRepeat ∈ FP ∧
    (∀ input, (polynomialBoundedPayloadRepeat input).length ≤
      2*input.length+6+(2*input.length+8)*(input.length+1)) ∧
    (∀ (ruler coefficient : List Bool) (bound : ℕ), bound ≤ ruler.length+1 →
      polynomialBoundedPayloadRepeat (pair ruler (pair bound.bits coefficient))=
        payloadListCode (List.replicate bound coefficient)) :=
  ⟨polynomial_bounded_payload_repeat_mem_fp,polynomial_bounded_payload_repeat_length,
    polynomial_bounded_payload_repeat_exact⟩
#print axioms polynomial_bounded_payload_repeat_exact
#print axioms bounded_payload_repeat_actual_polytime
end IV04.Paper.Computational
