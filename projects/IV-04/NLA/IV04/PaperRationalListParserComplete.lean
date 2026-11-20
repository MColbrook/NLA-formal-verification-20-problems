module

public import NLA.IV04.PaperRationalListOutputSemantics
public import NLA.IV04.PaperRationalListMachinePoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem rational_list_state_flag_boolean (input : List Bool) :
    countedFlag (rationalListState input)=[true] ∨ countedFlag (rationalListState input)=[false] := by
  obtain ⟨c,b,r,o,he,_,_,_⟩ := rational_list_iterate_shape input.length
    (canonicalWord (pairFst input)) (pairSnd input) [] true
  have hs : rationalListState input=countedPack c [b] r o := he
  rw [hs]
  cases b <;> simp [countedFlag,countedPack]

theorem rational_list_parser_result_eq_state (input : List Bool) :
    rationalListParserResult input=rationalListStateResult (rationalListState input) := by
  simp only [rationalListParserResult,encodedRationalListParser,pairFst_pair,pairSnd_pair,
    rationalListStateResult,canonical_nonempty_flag]
  obtain hf | hf := rational_list_state_flag_boolean input <;>
    by_cases hz : wordValue (countedCount (rationalListState input))=0 <;>
    simp [hf,hz,caseBit₀]

set_option maxHeartbeats 2000000 in
theorem rational_list_parser_exact (input : List Bool) :
    rationalListParserResult input=readRationals (wordValue (pairFst input)) (pairSnd input) := by
  rw [rational_list_parser_result_eq_state]
  have he := rational_list_iterate_run input.length (canonicalWord (pairFst input)) (pairSnd input) true []
  have hs : rationalListState input=rationalListRun input.length
      (canonicalWord (pairFst input)) true (pairSnd input) [] := he
  rw [hs,rational_list_run_result]
  simp only [canonical_word_value,List.map_nil,List.reverse_nil,List.nil_append,if_true]
  have hf := fuel_read_rationals_exact input.length (wordValue (pairFst input)) (pairSnd input)
    (pairSnd_length_le input)
  rw [hf]
  cases readRationals (wordValue (pairFst input)) (pairSnd input) <;> rfl

theorem rational_list_parser_actual_polytime : encodedRationalListParser ∈ FP ∧
    ∀ input, rationalListParserResult input=readRationals (wordValue (pairFst input)) (pairSnd input) :=
  ⟨encoded_rational_list_parser_mem_fp,rational_list_parser_exact⟩

theorem read_rationals_codes (values : List ℚ) (tail : List Bool) :
    readRationals values.length (values.flatMap IV04.Paper.rationalCode ++ tail)=some (values,tail) := by
  induction values with
  | nil => rfl
  | cons q values ih =>
    simp only [List.length_cons,List.flatMap_cons,List.append_assoc,readRationals,
      IV04.Paper.read_rational_code,bind,Option.bind_some,ih,Option.pure_def]

theorem rational_list_parser_actual_codes (values : List ℚ) (tail : List Bool) :
    rationalListParserResult (pair values.length.bits (values.flatMap IV04.Paper.rationalCode ++ tail))=
      some (values,tail) := by
  rw [rational_list_parser_exact,pairFst_pair,pairSnd_pair,word_value_foldr,
    IV04.Paper.bits_foldr]
  exact read_rationals_codes values tail

theorem rational_list_run_payload_shape (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool))
    (hpositive : ∀ w ∈ payloads, 0 < wordValue (pairSnd w)) :
    ∃ c b r ps, rationalListRun fuel count valid rest payloads=countedPack c [b] r (payloadListCode ps) ∧
      ∀ w ∈ ps, 0 < wordValue (pairSnd w) := by
  induction fuel generalizing count rest valid payloads with
  | zero => exact ⟨count,valid,rest,payloads,rfl,hpositive⟩
  | succ fuel ih =>
    simp only [rationalListRun]
    split_ifs with hz hv hp
    · exact ih count rest valid payloads hpositive
    · have hd : 0 < wordValue (pairSnd (pairFst (pairSnd (encodedRationalParser rest)))) := by
        rw [rational_parser_fraction]
        exact rational_parser_denominator_positive rest
      exact ih (decrementCount count) (pairSnd (pairSnd (encodedRationalParser rest))) true
        (pairFst (pairSnd (encodedRationalParser rest)) :: payloads) (by
          intro w hw
          rcases List.mem_cons.mp hw with he | hw
          · subst w; exact hd
          · exact hpositive w hw)
    · exact ih count rest false payloads hpositive
    · exact ih count rest valid payloads hpositive

theorem rational_list_state_payload_shape (input : List Bool) :
    ∃ c b r ps, rationalListState input=countedPack c [b] r (payloadListCode ps) ∧
      ∀ w ∈ ps, 0 < wordValue (pairSnd w) := by
  have he := rational_list_iterate_run input.length (canonicalWord (pairFst input)) (pairSnd input) true []
  have hs : rationalListState input=rationalListRun input.length
      (canonicalWord (pairFst input)) true (pairSnd input) [] := he
  rw [hs]
  exact rational_list_run_payload_shape _ _ _ _ _ (by simp)

theorem rational_list_parser_payload_shape (input : List Bool) :
    ∃ b ps rest, encodedRationalListParser input=pair [b] (pair (payloadListCode ps) rest) ∧
      ∀ w ∈ ps, 0 < wordValue (pairSnd w) := by
  obtain ⟨c,b,r,ps,hs,hp⟩ := rational_list_state_payload_shape input
  simp only [encodedRationalListParser,hs,countedCount,countedFlag,countedOutput,countedRest,
    countedPack,pairFst_pair,pairSnd_pair,canonical_nonempty_flag]
  by_cases hz : wordValue c=0
  · exact ⟨b,ps,r,by simp [hz,caseBit₀],hp⟩
  · exact ⟨false,ps,r,by simp [hz,caseBit₀],hp⟩

#print axioms rational_list_parser_actual_polytime
end IV04.Paper.Computational
