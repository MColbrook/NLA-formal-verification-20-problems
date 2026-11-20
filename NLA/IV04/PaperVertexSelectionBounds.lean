module

public import NLA.IV04.PaperVertexSelectionStep
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem vertex_selection_step_shape (count fields choices output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (f q o : List Bool),
      vertexSelectionStep (vertexSelectionPack count [valid] fields choices output)=
        vertexSelectionPack c [b] f q o ∧
      c.length ≤ count.length ∧ q.length ≤ choices.length ∧
      2*f.length+o.length ≤ 2*fields.length+output.length+2 := by
  let P : List Bool → Prop := fun state => ∃ (c : List Bool) (b : Bool) (f q o : List Bool),
      state=vertexSelectionPack c [b] f q o ∧
      c.length ≤ count.length ∧ q.length ≤ choices.length ∧
      2*f.length+o.length ≤ 2*fields.length+output.length+2
  have same : P (vertexSelectionPack count [valid] fields choices output) :=
    ⟨count,valid,fields,choices,output,rfl,le_refl _,le_refl _,by omega⟩
  change P (vertexSelectionStep (vertexSelectionPack count [valid] fields choices output))
  rw [vertex_selection_step_pack]
  apply case_bit_zero_property (P:=P)
  · cases valid
    · exact same
    · change P (caseBit₀ (vertexSelectionReady fields choices)
          (vertexSelectionPack (decrementCount count) [true] (pairSnd (pairSnd fields))
            choices.tail (pair (vertexSelectedWord fields choices) output))
          (vertexSelectionPack count [false] fields choices output))
      apply case_bit_zero_property (P:=P)
      · refine ⟨_,true,_,_,_,rfl,decrement_count_length count,?_,?_⟩
        · simp only [List.length_tail]; omega
        · have h1 := pair_projection_budget fields
          have h2 := pair_projection_budget (pairSnd fields)
          have hs := vertex_selected_word_length fields choices
          simp only [pair_length]
          omega
      · exact ⟨count,false,fields,choices,output,rfl,le_refl _,le_refl _,by omega⟩
  · exact same

theorem vertex_selection_iterate_shape (k : ℕ) (count fields choices output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (f q o : List Bool),
      (vertexSelectionStep^[k]) (vertexSelectionPack count [valid] fields choices output)=
        vertexSelectionPack c [b] f q o ∧
      c.length ≤ count.length ∧ q.length ≤ choices.length ∧
      2*f.length+o.length ≤ 2*fields.length+output.length+2*k := by
  induction k with
  | zero => exact ⟨count,valid,fields,choices,output,rfl,le_refl _,le_refl _,by omega⟩
  | succ k ih =>
    obtain ⟨c,b,f,q,o,he,hc,hq,hl⟩ := ih
    obtain ⟨c',b',f',q',o',hs,hc',hq',hl'⟩ := vertex_selection_step_shape c f q o b
    refine ⟨c',b',f',q',o',?_,hc'.trans hc,hq'.trans hq,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

theorem vertex_selection_iterate_length (k : ℕ) (count fields choices output : List Bool) (valid : Bool) :
    ((vertexSelectionStep^[k]) (vertexSelectionPack count [valid] fields choices output)).length ≤
      2*count.length+2*fields.length+2*choices.length+output.length+10+2*k := by
  obtain ⟨c,b,f,q,o,he,hc,hq,hl⟩ := vertex_selection_iterate_shape k count fields choices output valid
  rw [he]
  simp only [vertexSelectionPack,pair_length,List.length_cons,List.length_nil]
  omega

theorem vertex_selection_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((vertexSelectionStep^[k]) (vertexSelectionInitial input)).length ≤ 2*input.length+10+2*k := by
  have h := vertex_selection_iterate_length k (canonicalWord (pairFst input))
    (pairFst (pairSnd input)) (pairSnd (pairSnd input)) [] true
  have hc := canonical_word_length (pairFst input)
  have h1 := pair_projection_budget input
  have h2 := pair_projection_budget (pairSnd input)
  change ((vertexSelectionStep^[k])
    (vertexSelectionPack (canonicalWord (pairFst input)) [true]
      (pairFst (pairSnd input)) (pairSnd (pairSnd input)) [])).length ≤ _
  simp only [List.length_nil] at h
  omega

theorem vertex_selection_state_length (input : List Bool) :
    (vertexSelectionState input).length ≤ 4*input.length+10 := by
  have h := vertex_selection_initial_iterate_length input.length input
  change ((vertexSelectionStep^[input.length]) (vertexSelectionInitial input)).length ≤ _
  omega

#print axioms vertex_selection_state_length
end IV04.Paper.Computational
