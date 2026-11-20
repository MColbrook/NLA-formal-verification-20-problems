module

public import NLA.IV04.PaperWordListProductSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_pair_projection_budget (input : List Bool) :
    (Complexity.pairFst input).length+(Complexity.pairSnd input).length ≤ input.length := by
  exact pair_projection_budget input

theorem verified_word_list_product_step_pair (rest product : List Bool) :
    wordListProductStep (Complexity.pair rest product)=
      if rest=[] then Complexity.pair rest product else
        Complexity.pair (Complexity.pairSnd rest) (canonicalWordMultiply product (Complexity.pairFst rest)) := by
  exact word_list_product_step_pair rest product

theorem verified_word_list_product_step_shape (rest product : List Bool) :
    ∃ r p : List Bool, wordListProductStep (Complexity.pair rest product)=Complexity.pair r p ∧
      (Complexity.pair r p).length ≤ (Complexity.pair rest product).length := by
  exact word_list_product_step_shape rest product

theorem verified_word_list_product_iterate_shape (k : ℕ) (rest product : List Bool) :
    ∃ r p : List Bool, (wordListProductStep^[k]) (Complexity.pair rest product)=Complexity.pair r p ∧
      (Complexity.pair r p).length ≤ (Complexity.pair rest product).length := by
  exact word_list_product_iterate_shape k rest product

theorem verified_word_list_product_iterate_length (k : ℕ) (rest product : List Bool) :
    ((wordListProductStep^[k]) (Complexity.pair rest product)).length ≤
      2*rest.length+product.length+2 := by
  exact word_list_product_iterate_length k rest product

theorem verified_word_list_product_step_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListProductStep (v 0) := by
  exact word_list_product_step_cobham

theorem verified_word_list_product_state_cobham :
    Cobham fun v : Fin 1 → List Bool => wordListProductState (v 0) := by
  exact word_list_product_state_cobham

theorem verified_polynomial_word_list_product_mem_fp : polynomialWordListProduct ∈ FP := by
  exact polynomial_word_list_product_mem_fp

theorem verified_payload_list_count_length (payloads : List (List Bool)) :
    payloads.length ≤ (payloadListCode payloads).length := by
  exact payload_list_count_length payloads

theorem verified_word_list_product_iterate_nil (k : ℕ) (product : List Bool) :
    (wordListProductStep^[k]) (Complexity.pair [] product)=Complexity.pair [] product := by
  exact word_list_product_iterate_nil k product

theorem verified_word_list_product_iteration_value (k : ℕ) (payloads : List (List Bool)) (product : List Bool)
    (h : payloads.length ≤ k) :
    wordValue (Complexity.pairSnd ((wordListProductStep^[k])
      (Complexity.pair (payloadListCode payloads) product)))=
      wordValue product*(payloads.map wordValue).prod := by
  exact word_list_product_iteration_value k payloads product h

theorem verified_polynomial_word_list_product_value (payloads : List (List Bool)) :
    wordValue (polynomialWordListProduct (payloadListCode payloads))=(payloads.map wordValue).prod := by
  exact polynomial_word_list_product_value payloads

theorem verified_word_list_product_actual_polytime : polynomialWordListProduct ∈ Complexity.FP ∧
    ∀ payloads, wordValue (polynomialWordListProduct (payloadListCode payloads))=(payloads.map wordValue).prod := by
  exact word_list_product_actual_polytime

#print axioms IV04.Paper.Computational.verified_pair_projection_budget
#print axioms IV04.Paper.Computational.verified_word_list_product_step_pair
#print axioms IV04.Paper.Computational.verified_word_list_product_step_shape
#print axioms IV04.Paper.Computational.verified_word_list_product_iterate_shape
#print axioms IV04.Paper.Computational.verified_word_list_product_iterate_length
#print axioms IV04.Paper.Computational.verified_word_list_product_step_cobham
#print axioms IV04.Paper.Computational.verified_word_list_product_state_cobham
#print axioms IV04.Paper.Computational.verified_polynomial_word_list_product_mem_fp
#print axioms IV04.Paper.Computational.verified_payload_list_count_length
#print axioms IV04.Paper.Computational.verified_word_list_product_iterate_nil
#print axioms IV04.Paper.Computational.verified_word_list_product_iteration_value
#print axioms IV04.Paper.Computational.verified_polynomial_word_list_product_value
#print axioms IV04.Paper.Computational.verified_word_list_product_actual_polytime
end IV04.Paper.Computational
