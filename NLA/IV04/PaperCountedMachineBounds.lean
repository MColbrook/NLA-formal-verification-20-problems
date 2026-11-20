module

public import NLA.IV04.PaperCountedMachineStep
public import NLA.IV04.PaperSignedOrderSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem natural_parser_success_budget (input : List Bool)
    (h : Complexity.pairFst (encodedNaturalParser input)=[true]) :
    (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))).length+
      (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))).length+1 ≤ input.length := by
  rw [natural_parser_flag,natural_parse_flag_stages] at h
  split_ifs at h with he hn <;> simp at h
  have hd : (input.drop (headerWord input).length).length > 0 := by
    cases hh : input.drop (headerWord input).length with
    | nil => exact (he hh).elim
    | cons b bits => simp
  rw [natural_parser_payload,natural_parser_tail]
  simp only [List.length_drop] at hd
  simp only [List.length_take,List.length_drop,naturalParseRest,List.length_tail,List.length_drop] at hn ⊢
  omega

theorem counted_step_pack (count rest output : List Bool) (valid : Bool) :
    countedStep (countedPack count [valid] rest output)=
      if wordValue count=0 then countedPack count [valid] rest output
      else if valid then
        if Complexity.pairFst (encodedNaturalParser rest)=[true] then
          countedPack (decrementCount count) [true]
            (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser rest)))
            (Complexity.pair (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser rest))) output)
        else countedPack count [false] rest output
      else countedPack count [valid] rest output := by
  simp only [countedStep,countedCount,countedFlag,countedRest,countedOutput,countedPack,
    Complexity.pairFst_pair,Complexity.pairSnd_pair,canonical_nonempty_flag]
  by_cases hz : wordValue count=0
  · simp [hz,Complexity.caseBit₀]
  · cases valid <;> obtain hp | hp := natural_parser_flag_boolean rest <;>
      simp [hz,hp,Complexity.caseBit₀]

theorem counted_step_shape (count rest output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (r o : List Bool),
      countedStep (countedPack count [valid] rest output)=countedPack c [b] r o ∧
      (countedPack c [b] r o).length ≤ (countedPack count [valid] rest output).length := by
  rw [counted_step_pack]
  split_ifs with hz hb hp
  · exact ⟨count,valid,rest,output,rfl,le_refl _⟩
  · refine ⟨decrementCount count,true,_,_,rfl,?_⟩
    have hc := decrement_count_length count
    have hr := natural_parser_success_budget rest hp
    simp only [countedPack,Complexity.pair_length,List.length_cons,List.length_nil]
    omega
  · refine ⟨count,false,rest,output,rfl,?_⟩
    simp [countedPack]
  · exact ⟨count,valid,rest,output,rfl,le_refl _⟩

theorem counted_iterate_shape (k : ℕ) (count rest output : List Bool) (valid : Bool) :
    ∃ (c : List Bool) (b : Bool) (r o : List Bool),
      (countedStep^[k]) (countedPack count [valid] rest output)=countedPack c [b] r o ∧
      (countedPack c [b] r o).length ≤ (countedPack count [valid] rest output).length := by
  induction k with
  | zero => exact ⟨count,valid,rest,output,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨c,b,r,o,he,hl⟩ := ih
    obtain ⟨c',b',r',o',hs,hbound⟩ := counted_step_shape c r o b
    refine ⟨c',b',r',o',?_,hbound.trans hl⟩
    rw [Function.iterate_succ_apply',he,hs]

theorem counted_iterate_length (k : ℕ) (count rest output : List Bool) (valid : Bool) :
    ((countedStep^[k]) (countedPack count [valid] rest output)).length ≤
      (countedPack count [valid] rest output).length := by
  obtain ⟨c,b,r,o,he,hl⟩ := counted_iterate_shape k count rest output valid
  rw [he]
  exact hl

theorem counted_initial_length (input : List Bool) : (countedInitial input).length ≤ 4*input.length+8 := by
  have hc := canonical_word_length (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input)))
  have hp := natural_parser_payload_length input
  have ht := natural_parser_tail_length input
  have hf : (Complexity.pairFst (encodedNaturalParser input)).length=1 := by
    obtain h | h := natural_parser_flag_boolean input <;> simp [h]
  simp only [countedInitial,countedPack,Complexity.pair_length,List.length_nil]
  omega

set_option maxHeartbeats 2000000 in
theorem counted_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((countedStep^[k]) (countedInitial input)).length ≤ 4*input.length+8 := by
  have hi := counted_initial_length input
  obtain hf | hf := natural_parser_flag_boolean input
  · have h := counted_iterate_length k
      (canonicalWord (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))))
      (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))) [] true
    have hi' := hi
    simp only [countedInitial,hf] at hi'
    simpa only [countedInitial,hf] using h.trans hi'
  · have h := counted_iterate_length k
      (canonicalWord (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))))
      (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))) [] false
    have hi' := hi
    simp only [countedInitial,hf] at hi'
    simpa only [countedInitial,hf] using h.trans hi'

theorem counted_machine_state_length (input : List Bool) :
    (countedMachineState input).length ≤ 4*input.length+8 :=
  counted_initial_iterate_length input.length input

#print axioms counted_machine_state_length
end IV04.Paper.Computational
