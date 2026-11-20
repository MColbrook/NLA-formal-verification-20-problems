module

public import NLA.IV04.PaperRationalListParserDefinitions
public import NLA.IV04.PaperRationalParserBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem rational_list_step_pack (count rest output : List Bool) (valid : Bool) :
    rationalListStep (countedPack count [valid] rest output)=
      if wordValue count=0 then countedPack count [valid] rest output
      else if valid then
        if Complexity.pairFst (encodedRationalParser rest)=[true] then
          countedPack (decrementCount count) [true]
            (Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser rest)))
            (Complexity.pair (Complexity.pairFst (Complexity.pairSnd (encodedRationalParser rest))) output)
        else countedPack count [false] rest output
      else countedPack count [valid] rest output := by
  simp only [rationalListStep,countedCount,countedFlag,countedRest,countedOutput,countedPack,
    Complexity.pairFst_pair,Complexity.pairSnd_pair,canonical_nonempty_flag]
  by_cases hz : wordValue count=0
  · simp [hz,Complexity.caseBit₀]
  · cases valid <;> obtain hp | hp := rational_parser_flag_boolean rest <;>
      simp [hz,hp,Complexity.caseBit₀]

theorem rational_list_step_shape (count rest output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (r o : List Bool),
      rationalListStep (countedPack count [valid] rest output)=countedPack c [b] r o ∧
      c.length ≤ count.length ∧ r.length ≤ rest.length ∧
      o.length ≤ output.length+4*rest.length+12 := by
  rw [rational_list_step_pack]
  split_ifs with hz hv hp
  · exact ⟨count,valid,rest,output,rfl,le_refl _,le_refl _,by omega⟩
  · refine ⟨decrementCount count,true,_,_,rfl,decrement_count_length count,
      rational_parser_tail_length rest,?_⟩
    have hf := rational_parser_fraction_length rest
    simp only [Complexity.pair_length,rational_parser_fraction]
    omega
  · exact ⟨count,false,rest,output,rfl,le_refl _,le_refl _,by omega⟩
  · exact ⟨count,valid,rest,output,rfl,le_refl _,le_refl _,by omega⟩

theorem rational_list_iterate_shape (k : ℕ) (count rest output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (r o : List Bool),
      (rationalListStep^[k]) (countedPack count [valid] rest output)=countedPack c [b] r o ∧
      c.length ≤ count.length ∧ r.length ≤ rest.length ∧
      o.length ≤ output.length+k*(4*rest.length+12) := by
  induction k with
  | zero => exact ⟨count,valid,rest,output,rfl,le_refl _,le_refl _,by omega⟩
  | succ k ih =>
    obtain ⟨c,b,r,o,he,hc,hr,ho⟩ := ih
    obtain ⟨c',b',r',o',hs,hc',hr',ho'⟩ := rational_list_step_shape c r o b
    refine ⟨c',b',r',o',?_,hc'.trans hc,hr'.trans hr,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · have h4 := Nat.mul_le_mul_left 4 hr
      nlinarith

theorem rational_list_iterate_length (k : ℕ) (count rest output : List Bool) (valid : Bool) :
    ((rationalListStep^[k]) (countedPack count [valid] rest output)).length ≤
      2*count.length+2*rest.length+output.length+8+k*(4*rest.length+12) := by
  obtain ⟨c,b,r,o,he,hc,hr,ho⟩ := rational_list_iterate_shape k count rest output valid
  rw [he]
  simp only [countedPack,Complexity.pair_length,List.length_cons,List.length_nil]
  omega

theorem rational_list_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((rationalListStep^[k]) (rationalListInitial input)).length ≤
      2*input.length+8+k*(4*input.length+12) := by
  have h := rational_list_iterate_length k (canonicalWord (Complexity.pairFst input))
    (Complexity.pairSnd input) [] true
  have hc := canonical_word_length (Complexity.pairFst input)
  have hp := pair_projection_budget input
  have hs := Complexity.pairSnd_length_le input
  have hm := Nat.mul_le_mul_left k (show 4*(Complexity.pairSnd input).length+12 ≤
      4*input.length+12 by omega)
  simp only [rationalListInitial]
  simp only [List.length_nil,Nat.add_zero] at h
  exact h.trans (by omega)

theorem rational_list_state_length (input : List Bool) :
    (rationalListState input).length ≤
      2*input.length+8+input.length*(4*input.length+12) :=
  rational_list_initial_iterate_length input.length input

#print axioms rational_list_state_length
end IV04.Paper.Computational
