module

public import NLA.IV04.PaperVertexSelectionPoly
public import NLA.IV04.PaperVertexSelectionReference
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem vertex_selection_finished_step (count fields choices output : List Bool)
    (h : wordValue count=0) :
    vertexSelectionStep (vertexSelectionPack count [true] fields choices output)=
      vertexSelectionPack count [true] fields choices output := by
  rw [vertex_selection_step_pack,canonical_nonempty_flag]
  simp [h,caseBit₀]

theorem vertex_selection_finished_iterate (k : ℕ) (count fields choices output : List Bool)
    (h : wordValue count=0) :
    (vertexSelectionStep^[k]) (vertexSelectionPack count [true] fields choices output)=
      vertexSelectionPack count [true] fields choices output := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,vertex_selection_finished_step count fields choices output h]

theorem vertex_selection_good_step (count lower upper fields output : List Bool)
    (choice : Bool) (choices : List Bool)
    (hc : wordValue count ≠ 0) (ho : signedWordValue lower ≤ signedWordValue upper) :
    vertexSelectionStep (vertexSelectionPack count [true] (pair lower (pair upper fields))
      (choice::choices) output)=
      vertexSelectionPack (decrementCount count) [true] fields choices
        (pair (if choice then upper else lower) output) := by
  rw [vertex_selection_step_pack,canonical_nonempty_flag,vertex_selection_ready_pair]
  cases choice <;> simp [hc,ho,caseBit₀,vertexSelectedWord,pairFst_pair,pairSnd_pair]

theorem vertex_selection_iterate_codes (k : ℕ) (rows : List (List Bool × List Bool))
    (count rest choices output : List Bool)
    (hc : wordValue count=rows.length) (ho : endpointWordsOrdered rows)
    (hq : rows.length ≤ choices.length) (hk : rows.length ≤ k) :
    ∃ c : List Bool, wordValue c=0 ∧
      (vertexSelectionStep^[k]) (vertexSelectionPack count [true] (endpointWordPairsCode rows rest) choices output)=
        vertexSelectionPack c [true] rest (choices.drop rows.length)
          (List.foldr pair output (selectedEndpointWords rows choices).reverse) := by
  induction k generalizing rows count rest choices output with
  | zero =>
    have hr : rows=[] := by cases rows <;> simp_all
    subst rows
    exact ⟨count,hc,by simp [endpointWordPairsCode,selectedEndpointWords]⟩
  | succ k ih =>
    cases rows with
    | nil =>
      refine ⟨count,hc,?_⟩
      simp only [endpointWordPairsCode,selectedEndpointWords,List.length_nil,List.drop_zero,List.reverse_nil,List.foldr_nil]
      exact vertex_selection_finished_iterate (k+1) count rest choices output hc
    | cons row rows =>
      obtain ⟨lower,upper⟩ := row
      cases choices with
      | nil => simp at hq
      | cons choice choices =>
        have hcount : wordValue count ≠ 0 := by simp only [List.length_cons] at hc; omega
        have horder : signedWordValue lower ≤ signedWordValue upper := ho (lower,upper) (by simp)
        have hrest : endpointWordsOrdered rows := by intro r hr; exact ho r (by simp [hr])
        have hd : wordValue (decrementCount count)=rows.length := by
          rw [decrement_count_value,hc,List.length_cons]; omega
        have hq' : rows.length ≤ choices.length := by simp only [List.length_cons] at hq; omega
        have hk' : rows.length ≤ k := by simp only [List.length_cons] at hk; omega
        obtain ⟨c,hzero,he⟩ := ih rows (decrementCount count) rest choices
          (pair (if choice then upper else lower) output) hd hrest hq' hk'
        refine ⟨c,hzero,?_⟩
        rw [Function.iterate_succ_apply]
        simp only [endpointWordPairsCode]
        rw [vertex_selection_good_step count lower upper (endpointWordPairsCode rows rest) output choice choices hcount horder,he]
        simp [selectedEndpointWords,List.reverse_cons,List.foldr_append]

theorem vertex_selection_input_codes (rows : List (List Bool × List Bool))
    (rest choices : List Bool) (ho : endpointWordsOrdered rows) (hq : rows.length ≤ choices.length) :
    encodedVertexSelection (vertexSelectionInputCode rows rest choices)=
      pair [true] (pair (payloadListCode (selectedEndpointWords rows choices).reverse)
        (pair rest (choices.drop rows.length))) := by
  have hbits : wordValue rows.length.bits=rows.length := by
    rw [word_value_foldr]; exact IV04.Paper.bits_foldr _
  have hc : wordValue (canonicalWord rows.length.bits)=rows.length := by rw [canonical_word_value,hbits]
  have hk : rows.length ≤ (vertexSelectionInputCode rows rest choices).length := by
    simp only [vertexSelectionInputCode,pair_length]
    omega
  obtain ⟨c,hzero,he⟩ := vertex_selection_iterate_codes
    (vertexSelectionInputCode rows rest choices).length rows (canonicalWord rows.length.bits)
    rest choices [] hc ho hq hk
  have hs : vertexSelectionState (vertexSelectionInputCode rows rest choices)=
      vertexSelectionPack c [true] rest (choices.drop rows.length)
        (List.foldr pair [] (selectedEndpointWords rows choices).reverse) := by
    simpa only [vertexSelectionState,vertexSelectionInitial,vertexSelectionInputCode,pairFst_pair,pairSnd_pair] using he
  simp only [encodedVertexSelection,hs,vertexSelectionCount,vertexSelectionFlag,vertexSelectionFields,
    vertexSelectionChoices,vertexSelectionOutput,vertexSelectionPack,pairFst_pair,pairSnd_pair,canonical_nonempty_flag,hzero,if_true]
  simp only [caseBit₀]
  have hfold : ∀ values : List (List Bool), List.foldr pair [] values=payloadListCode values := by
    intro values; induction values with
    | nil => rfl
    | cons value values ih => simp [payloadListCode,ih]
  rw [hfold]

#print axioms vertex_selection_input_codes
end IV04.Paper.Computational
