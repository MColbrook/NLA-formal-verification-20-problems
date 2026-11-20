module

public import NLA.IV04.PaperCountedOutputSemantics
public import NLA.IV04.PaperCountedMachinePoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

set_option maxHeartbeats 2000000 in
theorem counted_machine_flag_boolean (input : List Bool) :
    countedFlag (countedMachineState input)=[true] ∨ countedFlag (countedMachineState input)=[false] := by
  obtain hf | hf := natural_parser_flag_boolean input
  · obtain ⟨c,b,r,o,he,_⟩ := counted_iterate_shape input.length
      (canonicalWord (pairFst (pairSnd (encodedNaturalParser input))))
      (pairSnd (pairSnd (encodedNaturalParser input))) [] true
    have hs : countedMachineState input=countedPack c [b] r o := by
      simpa only [countedMachineState,countedInitial,hf] using he
    rw [hs]
    cases b <;> simp [countedFlag,countedPack]
  · obtain ⟨c,b,r,o,he,_⟩ := counted_iterate_shape input.length
      (canonicalWord (pairFst (pairSnd (encodedNaturalParser input))))
      (pairSnd (pairSnd (encodedNaturalParser input))) [] false
    have hs : countedMachineState input=countedPack c [b] r o := by
      simpa only [countedMachineState,countedInitial,hf] using he
    rw [hs]
    cases b <;> simp [countedFlag,countedPack]

theorem counted_parser_result_eq_state (input : List Bool) :
    countedParserResult input=countedStateResult (countedMachineState input) := by
  simp only [countedParserResult,encodedCountedNaturalParser,pairFst_pair,pairSnd_pair,
    countedStateResult,canonical_nonempty_flag]
  obtain hf | hf := counted_machine_flag_boolean input <;>
    by_cases hz : wordValue (countedCount (countedMachineState input))=0 <;>
    simp [hf,hz,caseBit₀]

set_option maxHeartbeats 2000000 in
theorem counted_parser_exact (input : List Bool) :
    countedParserResult input=IV04.Paper.readIntegerWeights input := by
  rw [counted_parser_result_eq_state]
  obtain hf | hf := natural_parser_flag_boolean input
  · have he := counted_iterate_run input.length
      (canonicalWord (pairFst (pairSnd (encodedNaturalParser input))))
      (pairSnd (pairSnd (encodedNaturalParser input))) true []
    have hs : countedMachineState input=countedRun input.length
        (canonicalWord (pairFst (pairSnd (encodedNaturalParser input)))) true
        (pairSnd (pairSnd (encodedNaturalParser input))) [] := by
      simpa only [countedMachineState,countedInitial,hf,payloadListCode] using he
    rw [hs,counted_run_result]
    simp only [canonical_word_value,eq_self_iff_true,if_true,List.map_nil,List.reverse_nil,List.nil_append]
    rw [fuel_read_naturals_exact input.length _ _ (natural_parser_tail_length input)]
    simp [IV04.Paper.readIntegerWeights,read_natural_of_flag_true input hf]
  · have he := counted_iterate_run input.length
      (canonicalWord (pairFst (pairSnd (encodedNaturalParser input))))
      (pairSnd (pairSnd (encodedNaturalParser input))) false []
    have hs : countedMachineState input=countedRun input.length
        (canonicalWord (pairFst (pairSnd (encodedNaturalParser input)))) false
        (pairSnd (pairSnd (encodedNaturalParser input))) [] := by
      simpa only [countedMachineState,countedInitial,hf,payloadListCode] using he
    rw [hs,counted_run_result]
    simp [IV04.Paper.readIntegerWeights,read_natural_of_flag_false input hf]

theorem counted_parser_actual_polytime : encodedCountedNaturalParser ∈ FP ∧
    ∀ input, countedParserResult input=IV04.Paper.readIntegerWeights input :=
  ⟨encoded_counted_natural_parser_mem_fp,counted_parser_exact⟩

#print axioms counted_parser_actual_polytime
end IV04.Paper.Computational
