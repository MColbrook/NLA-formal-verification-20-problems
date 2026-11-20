module

public import NLA.IV04.PaperVertexSelectionRejection
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_vertex_selection_pack_cobham {n : ℕ}
    {count flag fields choices output : (Fin n → List Bool) → List Bool}
    (hc : Cobham count) (hf : Cobham flag) (ht : Cobham fields)
    (hb : Cobham choices) (ho : Cobham output) :
    Cobham fun v => vertexSelectionPack (count v) (flag v) (fields v) (choices v) (output v) := by
  exact vertex_selection_pack_cobham hc hf ht hb ho

theorem verified_vertex_selection_ready_cobham :
    Cobham fun v : Fin 2 → List Bool => vertexSelectionReady (v 0) (v 1) := by
  exact vertex_selection_ready_cobham

theorem verified_vertex_selected_word_cobham :
    Cobham fun v : Fin 2 → List Bool => vertexSelectedWord (v 0) (v 1) := by
  exact vertex_selected_word_cobham

theorem verified_vertex_selected_word_length (fields choices : List Bool) :
    (vertexSelectedWord fields choices).length ≤
      (pairFst fields).length+(pairFst (pairSnd fields)).length := by
  exact vertex_selected_word_length fields choices

theorem verified_vertex_selected_word_value (lower upper rest : List Bool) (choice : Bool) (choices : List Bool) :
    signedWordValue (vertexSelectedWord (pair lower (pair upper rest)) (choice::choices))=
      if choice then signedWordValue upper else signedWordValue lower := by
  exact vertex_selected_word_value lower upper rest choice choices

theorem verified_vertex_selection_pair_nonempty_flag (left right : List Bool) :
    nonemptyFlag (pair left right)=[true] := by
  exact vertex_selection_pair_nonempty_flag left right

theorem verified_vertex_selection_ready_pair (lower upper rest : List Bool) (choice : Bool) (choices : List Bool) :
    vertexSelectionReady (pair lower (pair upper rest)) (choice::choices)=
      [decide (signedWordValue lower ≤ signedWordValue upper)] := by
  exact vertex_selection_ready_pair lower upper rest choice choices

theorem verified_vertex_selection_step_pack (count flag fields choices output : List Bool) :
    vertexSelectionStep (vertexSelectionPack count flag fields choices output)=
      caseBit₀ (nonemptyFlag (canonicalWord count))
        (caseBit₀ flag (caseBit₀ (vertexSelectionReady fields choices)
          (vertexSelectionPack (decrementCount count) [true] (pairSnd (pairSnd fields))
            choices.tail (pair (vertexSelectedWord fields choices) output))
          (vertexSelectionPack count [false] fields choices output))
          (vertexSelectionPack count flag fields choices output))
        (vertexSelectionPack count flag fields choices output) := by
  exact vertex_selection_step_pack count flag fields choices output

theorem verified_vertex_selection_step_cobham :
    Cobham fun v : Fin 1 → List Bool => vertexSelectionStep (v 0) := by
  exact vertex_selection_step_cobham

theorem verified_vertex_selection_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => vertexSelectionInitial (v 0) := by
  exact vertex_selection_initial_cobham

theorem verified_vertex_selection_step_shape (count fields choices output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (f q o : List Bool),
      vertexSelectionStep (vertexSelectionPack count [valid] fields choices output)=
        vertexSelectionPack c [b] f q o ∧
      c.length ≤ count.length ∧ q.length ≤ choices.length ∧
      2*f.length+o.length ≤ 2*fields.length+output.length+2 := by
  exact vertex_selection_step_shape count fields choices output valid

theorem verified_vertex_selection_iterate_shape (k : ℕ) (count fields choices output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (f q o : List Bool),
      (vertexSelectionStep^[k]) (vertexSelectionPack count [valid] fields choices output)=
        vertexSelectionPack c [b] f q o ∧
      c.length ≤ count.length ∧ q.length ≤ choices.length ∧
      2*f.length+o.length ≤ 2*fields.length+output.length+2*k := by
  exact vertex_selection_iterate_shape k count fields choices output valid

theorem verified_vertex_selection_iterate_length (k : ℕ) (count fields choices output : List Bool) (valid : Bool) :
    ((vertexSelectionStep^[k]) (vertexSelectionPack count [valid] fields choices output)).length ≤
      2*count.length+2*fields.length+2*choices.length+output.length+10+2*k := by
  exact vertex_selection_iterate_length k count fields choices output valid

theorem verified_vertex_selection_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((vertexSelectionStep^[k]) (vertexSelectionInitial input)).length ≤ 2*input.length+10+2*k := by
  exact vertex_selection_initial_iterate_length k input

theorem verified_vertex_selection_state_length (input : List Bool) :
    (vertexSelectionState input).length ≤ 4*input.length+10 := by
  exact vertex_selection_state_length input

theorem verified_vertex_selection_state_cobham :
    Cobham fun v : Fin 1 → List Bool => vertexSelectionState (v 0) := by
  exact vertex_selection_state_cobham

theorem verified_encoded_vertex_selection_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedVertexSelection (v 0) := by
  exact encoded_vertex_selection_cobham

theorem verified_encoded_vertex_selection_mem_fp : encodedVertexSelection ∈ FP := by
  exact encoded_vertex_selection_mem_fp

theorem verified_vertex_selection_finished_step (count fields choices output : List Bool)
    (h : wordValue count=0) :
    vertexSelectionStep (vertexSelectionPack count [true] fields choices output)=
      vertexSelectionPack count [true] fields choices output := by
  exact vertex_selection_finished_step count fields choices output h

theorem verified_vertex_selection_finished_iterate (k : ℕ) (count fields choices output : List Bool)
    (h : wordValue count=0) :
    (vertexSelectionStep^[k]) (vertexSelectionPack count [true] fields choices output)=
      vertexSelectionPack count [true] fields choices output := by
  exact vertex_selection_finished_iterate k count fields choices output h

theorem verified_vertex_selection_good_step (count lower upper fields output : List Bool)
    (choice : Bool) (choices : List Bool)
    (hc : wordValue count ≠ 0) (ho : signedWordValue lower ≤ signedWordValue upper) :
    vertexSelectionStep (vertexSelectionPack count [true] (pair lower (pair upper fields))
      (choice::choices) output)=
      vertexSelectionPack (decrementCount count) [true] fields choices
        (pair (if choice then upper else lower) output) := by
  exact vertex_selection_good_step count lower upper fields output choice choices hc ho

theorem verified_vertex_selection_iterate_codes (k : ℕ) (rows : List (List Bool × List Bool))
    (count rest choices output : List Bool)
    (hc : wordValue count=rows.length) (ho : endpointWordsOrdered rows)
    (hq : rows.length ≤ choices.length) (hk : rows.length ≤ k) :
    ∃ c : List Bool, wordValue c=0 ∧
      (vertexSelectionStep^[k]) (vertexSelectionPack count [true] (endpointWordPairsCode rows rest) choices output)=
        vertexSelectionPack c [true] rest (choices.drop rows.length)
          (List.foldr pair output (selectedEndpointWords rows choices).reverse) := by
  exact vertex_selection_iterate_codes k rows count rest choices output hc ho hq hk

theorem verified_vertex_selection_input_codes (rows : List (List Bool × List Bool))
    (rest choices : List Bool) (ho : endpointWordsOrdered rows) (hq : rows.length ≤ choices.length) :
    encodedVertexSelection (vertexSelectionInputCode rows rest choices)=
      pair [true] (pair (payloadListCode (selectedEndpointWords rows choices).reverse)
        (pair rest (choices.drop rows.length))) := by
  exact vertex_selection_input_codes rows rest choices ho hq

theorem verified_vertex_selection_failed_step (count fields choices output : List Bool) :
    vertexSelectionStep (vertexSelectionPack count [false] fields choices output)=
      vertexSelectionPack count [false] fields choices output := by
  exact vertex_selection_failed_step count fields choices output

theorem verified_vertex_selection_failed_iterate (k : ℕ) (count fields choices output : List Bool) :
    (vertexSelectionStep^[k]) (vertexSelectionPack count [false] fields choices output)=
      vertexSelectionPack count [false] fields choices output := by
  exact vertex_selection_failed_iterate k count fields choices output

theorem verified_vertex_selection_not_ready_step (count fields choices output : List Bool)
    (hc : wordValue count ≠ 0) (hr : vertexSelectionReady fields choices=[false]) :
    vertexSelectionStep (vertexSelectionPack count [true] fields choices output)=
      vertexSelectionPack count [false] fields choices output := by
  exact vertex_selection_not_ready_step count fields choices output hc hr

theorem verified_vertex_selection_not_ready_iterate (k : ℕ) (count fields choices output : List Bool)
    (hc : wordValue count ≠ 0) (hr : vertexSelectionReady fields choices=[false]) :
    (vertexSelectionStep^[k+1]) (vertexSelectionPack count [true] fields choices output)=
      vertexSelectionPack count [false] fields choices output := by
  exact vertex_selection_not_ready_iterate k count fields choices output hc hr

theorem verified_vertex_selection_missing_choices (fields : List Bool) :
    vertexSelectionReady fields []=[false] := by
  exact vertex_selection_missing_choices fields

theorem verified_vertex_selection_unordered_ready (lower upper rest choices : List Bool)
    (h : ¬signedWordValue lower ≤ signedWordValue upper) :
    vertexSelectionReady (pair lower (pair upper rest)) choices=[false] := by
  exact vertex_selection_unordered_ready lower upper rest choices h

theorem verified_selected_endpoint_words_length (rows : List (List Bool × List Bool)) (choices : List Bool) :
    (selectedEndpointWords rows choices).length=rows.length := by
  exact selected_endpoint_words_length rows choices

theorem verified_vertex_selection_actual_polytime : encodedVertexSelection ∈ FP ∧
    ∀ (rows : List (List Bool × List Bool)) (rest choices : List Bool),
      endpointWordsOrdered rows → rows.length ≤ choices.length →
      encodedVertexSelection (vertexSelectionInputCode rows rest choices)=
        pair [true] (pair (payloadListCode (selectedEndpointWords rows choices).reverse)
          (pair rest (choices.drop rows.length))) := by
  exact vertex_selection_actual_polytime

#print axioms IV04.Paper.Computational.verified_vertex_selection_pack_cobham
#print axioms IV04.Paper.Computational.verified_vertex_selection_ready_cobham
#print axioms IV04.Paper.Computational.verified_vertex_selected_word_cobham
#print axioms IV04.Paper.Computational.verified_vertex_selected_word_length
#print axioms IV04.Paper.Computational.verified_vertex_selected_word_value
#print axioms IV04.Paper.Computational.verified_vertex_selection_pair_nonempty_flag
#print axioms IV04.Paper.Computational.verified_vertex_selection_ready_pair
#print axioms IV04.Paper.Computational.verified_vertex_selection_step_pack
#print axioms IV04.Paper.Computational.verified_vertex_selection_step_cobham
#print axioms IV04.Paper.Computational.verified_vertex_selection_initial_cobham
#print axioms IV04.Paper.Computational.verified_vertex_selection_step_shape
#print axioms IV04.Paper.Computational.verified_vertex_selection_iterate_shape
#print axioms IV04.Paper.Computational.verified_vertex_selection_iterate_length
#print axioms IV04.Paper.Computational.verified_vertex_selection_initial_iterate_length
#print axioms IV04.Paper.Computational.verified_vertex_selection_state_length
#print axioms IV04.Paper.Computational.verified_vertex_selection_state_cobham
#print axioms IV04.Paper.Computational.verified_encoded_vertex_selection_cobham
#print axioms IV04.Paper.Computational.verified_encoded_vertex_selection_mem_fp
#print axioms IV04.Paper.Computational.verified_vertex_selection_finished_step
#print axioms IV04.Paper.Computational.verified_vertex_selection_finished_iterate
#print axioms IV04.Paper.Computational.verified_vertex_selection_good_step
#print axioms IV04.Paper.Computational.verified_vertex_selection_iterate_codes
#print axioms IV04.Paper.Computational.verified_vertex_selection_input_codes
#print axioms IV04.Paper.Computational.verified_vertex_selection_failed_step
#print axioms IV04.Paper.Computational.verified_vertex_selection_failed_iterate
#print axioms IV04.Paper.Computational.verified_vertex_selection_not_ready_step
#print axioms IV04.Paper.Computational.verified_vertex_selection_not_ready_iterate
#print axioms IV04.Paper.Computational.verified_vertex_selection_missing_choices
#print axioms IV04.Paper.Computational.verified_vertex_selection_unordered_ready
#print axioms IV04.Paper.Computational.verified_selected_endpoint_words_length
#print axioms IV04.Paper.Computational.verified_vertex_selection_actual_polytime
end IV04.Paper.Computational
