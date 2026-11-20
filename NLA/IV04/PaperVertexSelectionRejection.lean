module

public import NLA.IV04.PaperVertexSelectionSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem vertex_selection_failed_step (count fields choices output : List Bool) :
    vertexSelectionStep (vertexSelectionPack count [false] fields choices output)=
      vertexSelectionPack count [false] fields choices output := by
  rw [vertex_selection_step_pack]
  apply case_bit_zero_property (P:=fun state => state=vertexSelectionPack count [false] fields choices output)
  · rfl
  · rfl

theorem vertex_selection_failed_iterate (k : ℕ) (count fields choices output : List Bool) :
    (vertexSelectionStep^[k]) (vertexSelectionPack count [false] fields choices output)=
      vertexSelectionPack count [false] fields choices output := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,vertex_selection_failed_step]

theorem vertex_selection_not_ready_step (count fields choices output : List Bool)
    (hc : wordValue count ≠ 0) (hr : vertexSelectionReady fields choices=[false]) :
    vertexSelectionStep (vertexSelectionPack count [true] fields choices output)=
      vertexSelectionPack count [false] fields choices output := by
  rw [vertex_selection_step_pack,canonical_nonempty_flag]
  simp [hc,hr,caseBit₀]

theorem vertex_selection_not_ready_iterate (k : ℕ) (count fields choices output : List Bool)
    (hc : wordValue count ≠ 0) (hr : vertexSelectionReady fields choices=[false]) :
    (vertexSelectionStep^[k+1]) (vertexSelectionPack count [true] fields choices output)=
      vertexSelectionPack count [false] fields choices output := by
  rw [Function.iterate_succ_apply,vertex_selection_not_ready_step count fields choices output hc hr]
  exact vertex_selection_failed_iterate k count fields choices output

theorem vertex_selection_missing_choices (fields : List Bool) :
    vertexSelectionReady fields []=[false] := by
  change andBit (nonemptyFlag fields) (andBit (nonemptyFlag (pairSnd fields)) [false])=[false]
  have hf : ∀ flag : List Bool, andBit flag [false]=[false] := by
    intro flag
    cases flag with
    | nil => rfl
    | cons b bits => cases b <;> rfl
  rw [hf,hf]

theorem vertex_selection_unordered_ready (lower upper rest choices : List Bool)
    (h : ¬signedWordValue lower ≤ signedWordValue upper) :
    vertexSelectionReady (pair lower (pair upper rest)) choices=[false] := by
  cases choices with
  | nil => exact vertex_selection_missing_choices _
  | cons choice choices => simp only [vertex_selection_ready_pair,h,decide_false]

theorem selected_endpoint_words_length (rows : List (List Bool × List Bool)) (choices : List Bool) :
    (selectedEndpointWords rows choices).length=rows.length := by
  induction rows generalizing choices with
  | nil => rfl
  | cons row rows ih => obtain ⟨lower,upper⟩ := row; simp [selectedEndpointWords,ih]

theorem vertex_selection_actual_polytime : encodedVertexSelection ∈ FP ∧
    ∀ (rows : List (List Bool × List Bool)) (rest choices : List Bool),
      endpointWordsOrdered rows → rows.length ≤ choices.length →
      encodedVertexSelection (vertexSelectionInputCode rows rest choices)=
        pair [true] (pair (payloadListCode (selectedEndpointWords rows choices).reverse)
          (pair rest (choices.drop rows.length))) :=
  ⟨encoded_vertex_selection_mem_fp,vertex_selection_input_codes⟩

#print axioms vertex_selection_actual_polytime
end IV04.Paper.Computational
