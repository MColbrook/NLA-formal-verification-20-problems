module

public import NLA.IV04.PaperWordListProductPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem payload_list_count_length (payloads : List (List Bool)) :
    payloads.length ≤ (payloadListCode payloads).length := by
  induction payloads with
  | nil => rfl
  | cons payload payloads ih => simp only [payloadListCode,Complexity.pair_length,List.length_cons]; omega

theorem word_list_product_iterate_nil (k : ℕ) (product : List Bool) :
    (wordListProductStep^[k]) (Complexity.pair [] product)=Complexity.pair [] product := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,word_list_product_step_pair]; simp

theorem word_list_product_iteration_value (k : ℕ) (payloads : List (List Bool)) (product : List Bool)
    (h : payloads.length ≤ k) :
    wordValue (Complexity.pairSnd ((wordListProductStep^[k])
      (Complexity.pair (payloadListCode payloads) product)))=
      wordValue product*(payloads.map wordValue).prod := by
  induction k generalizing payloads product with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,word_list_product_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h; omega
      have hn : Complexity.pair payload (payloadListCode payloads) ≠ [] := by
        intro he
        have hl := congrArg List.length he
        simp only [Complexity.pair_length,List.length_nil] at hl
        omega
      rw [Function.iterate_succ_apply,word_list_product_step_pair]
      simp only [payloadListCode,hn,if_false,Complexity.pairFst_pair,Complexity.pairSnd_pair]
      rw [ih payloads (canonicalWordMultiply product payload) ht,canonical_word_multiply_value]
      simp [Nat.mul_assoc]

theorem polynomial_word_list_product_value (payloads : List (List Bool)) :
    wordValue (polynomialWordListProduct (payloadListCode payloads))=(payloads.map wordValue).prod := by
  have h := word_list_product_iteration_value (payloadListCode payloads).length payloads [true]
    (payload_list_count_length payloads)
  simpa [polynomialWordListProduct,wordListProductState,wordValue,bitValue] using h

theorem word_list_product_actual_polytime : polynomialWordListProduct ∈ Complexity.FP ∧
    ∀ payloads, wordValue (polynomialWordListProduct (payloadListCode payloads))=(payloads.map wordValue).prod :=
  ⟨polynomial_word_list_product_mem_fp,polynomial_word_list_product_value⟩

#print axioms word_list_product_actual_polytime
end IV04.Paper.Computational
