module

public import NLA.IV04.PaperVertexSelectionRejection
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem endpoint_word_pairs_code_count_length (rows : List (List Bool × List Bool)) (rest : List Bool) :
    rows.length ≤ (endpointWordPairsCode rows rest).length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    obtain ⟨lower,upper⟩ := row
    simp only [endpointWordPairsCode,List.length_cons,pair_length]
    omega

theorem vertex_selection_invalid_iterate_codes (k : ℕ) (rows : List (List Bool × List Bool))
    (count rest choices output : List Bool) (hc : wordValue count=rows.length)
    (hk : rows.length ≤ k) (hbad : ¬(endpointWordsOrdered rows ∧ rows.length ≤ choices.length)) :
    ∃ c fields cert out : List Bool,
      (vertexSelectionStep^[k]) (vertexSelectionPack count [true] (endpointWordPairsCode rows rest) choices output)=
        vertexSelectionPack c [false] fields cert out := by
  induction k generalizing rows count rest choices output with
  | zero =>
    have hr : rows=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hk)
    subst rows
    exact False.elim (hbad ⟨by simp [endpointWordsOrdered],by simp⟩)
  | succ k ih =>
    cases rows with
    | nil => exact False.elim (hbad ⟨by simp [endpointWordsOrdered],by simp⟩)
    | cons row rows =>
      obtain ⟨lower,upper⟩ := row
      have hn : wordValue count≠0 := by simp only [List.length_cons] at hc;omega
      cases choices with
      | nil =>
        refine ⟨count,endpointWordPairsCode ((lower,upper)::rows) rest,[],output,?_⟩
        exact vertex_selection_not_ready_iterate k count _ [] output hn (vertex_selection_missing_choices _)
      | cons choice choices =>
        by_cases ho : signedWordValue lower ≤ signedWordValue upper
        · have htail : ¬(endpointWordsOrdered rows ∧ rows.length ≤ choices.length) := by
            rintro ⟨ht,hq⟩
            apply hbad
            refine ⟨?_,by simpa using hq⟩
            intro row hr
            rcases List.mem_cons.mp hr with he|he
            · simpa [he] using ho
            · exact ht row he
          have hd : wordValue (decrementCount count)=rows.length := by
            rw [decrement_count_value,hc,List.length_cons];omega
          have hk' : rows.length ≤ k := by simp only [List.length_cons] at hk;omega
          obtain ⟨c,fields,cert,out,he⟩ := ih rows (decrementCount count) rest choices
            (pair (if choice then upper else lower) output) hd hk' htail
          refine ⟨c,fields,cert,out,?_⟩
          rw [Function.iterate_succ_apply]
          simp only [endpointWordPairsCode]
          rw [vertex_selection_good_step count lower upper (endpointWordPairsCode rows rest) output choice choices hn ho]
          exact he
        · refine ⟨count,endpointWordPairsCode ((lower,upper)::rows) rest,choice::choices,output,?_⟩
          exact vertex_selection_not_ready_iterate k count _ _ output hn
            (vertex_selection_unordered_ready lower upper _ _ ho)

theorem vertex_selection_invalid_input_flag (rows : List (List Bool × List Bool)) (rest choices : List Bool)
    (hbad : ¬(endpointWordsOrdered rows ∧ rows.length ≤ choices.length)) :
    pairFst (encodedVertexSelection (vertexSelectionInputCode rows rest choices))=[false] := by
  have hc : wordValue (canonicalWord rows.length.bits)=rows.length := by
    rw [canonical_word_value,word_value_foldr];exact IV04.Paper.bits_foldr _
  have hb := endpoint_word_pairs_code_count_length rows rest
  have hk : rows.length ≤ (vertexSelectionInputCode rows rest choices).length := by
    simp only [vertexSelectionInputCode,pair_length];omega
  obtain ⟨c,fields,cert,out,he⟩ := vertex_selection_invalid_iterate_codes
    (vertexSelectionInputCode rows rest choices).length rows (canonicalWord rows.length.bits) rest choices [] hc hk hbad
  have hs : vertexSelectionState (vertexSelectionInputCode rows rest choices)=vertexSelectionPack c [false] fields cert out := by
    simpa only [vertexSelectionState,vertexSelectionInitial,vertexSelectionInputCode,pairFst_pair,pairSnd_pair] using he
  simp only [encodedVertexSelection,hs,pairFst_pair,vertexSelectionCount,vertexSelectionFlag,
    vertexSelectionPack,pairFst_pair,pairSnd_pair]
  apply case_bit_zero_property (P:=fun flag => flag=[false]) <;> rfl

#print axioms vertex_selection_invalid_input_flag
end IV04.Paper.Computational