module

public import NLA.IV04.PaperPositiveWeightParserDefinitions
public import NLA.IV04.PaperWordListPositive
public import NLA.IV04.PaperCountedParserComplete
public import NLA.IV04.PaperInputEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem counted_run_payload_shape (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    ∃ c b r ps, countedRun fuel count valid rest payloads=countedPack c [b] r (payloadListCode ps) := by
  induction fuel generalizing count rest valid payloads with
  | zero => exact ⟨count,valid,rest,payloads,rfl⟩
  | succ fuel ih =>
    simp only [countedRun]
    split_ifs with hz hv hp
    · exact ih count rest valid payloads
    · exact ih (decrementCount count)
        (pairSnd (pairSnd (encodedNaturalParser rest))) true
        (pairFst (pairSnd (encodedNaturalParser rest)) :: payloads)
    · exact ih count rest false payloads
    · exact ih count rest valid payloads

set_option maxHeartbeats 2000000 in
theorem counted_machine_payload_shape (input : List Bool) :
    ∃ c b r ps, countedMachineState input=countedPack c [b] r (payloadListCode ps) := by
  obtain hf | hf := natural_parser_flag_boolean input
  · have he := counted_iterate_run input.length
      (canonicalWord (pairFst (pairSnd (encodedNaturalParser input))))
      (pairSnd (pairSnd (encodedNaturalParser input))) true []
    have hs : countedMachineState input=countedRun input.length
        (canonicalWord (pairFst (pairSnd (encodedNaturalParser input)))) true
        (pairSnd (pairSnd (encodedNaturalParser input))) [] := by
      simpa only [countedMachineState,countedInitial,hf,payloadListCode] using he
    rw [hs]
    exact counted_run_payload_shape _ _ _ _ _
  · have he := counted_iterate_run input.length
      (canonicalWord (pairFst (pairSnd (encodedNaturalParser input))))
      (pairSnd (pairSnd (encodedNaturalParser input))) false []
    have hs : countedMachineState input=countedRun input.length
        (canonicalWord (pairFst (pairSnd (encodedNaturalParser input)))) false
        (pairSnd (pairSnd (encodedNaturalParser input))) [] := by
      simpa only [countedMachineState,countedInitial,hf,payloadListCode] using he
    rw [hs]
    exact counted_run_payload_shape _ _ _ _ _

theorem counted_parser_payload_shape (input : List Bool) :
    ∃ b ps rest, encodedCountedNaturalParser input=pair [b] (pair (payloadListCode ps) rest) := by
  obtain ⟨c,b,r,ps,hs⟩ := counted_machine_payload_shape input
  simp only [encodedCountedNaturalParser,hs,countedCount,countedFlag,countedOutput,countedRest,
    countedPack,pairFst_pair,pairSnd_pair,canonical_nonempty_flag]
  by_cases hz : wordValue c=0
  · exact ⟨b,ps,r,by simp [hz,caseBit₀]⟩
  · exact ⟨false,ps,r,by simp [hz,caseBit₀]⟩

theorem payload_positive_reverse (ps : List (List Bool)) :
    ((ps.map wordValue).reverse ≠ [] ∧ ∀ w ∈ (ps.map wordValue).reverse, 0 < w) ↔
      (ps ≠ [] ∧ ∀ w ∈ ps, 0 < wordValue w) := by
  have he : (ps.map wordValue).reverse ≠ [] ↔ ps ≠ [] := by
    constructor
    · intro hn h
      rw [h] at hn
      simp at hn
    · intro hn h
      have hl := congrArg List.length h
      simp only [List.length_reverse,List.length_map,List.length_nil] at hl
      cases ps with
      | nil => exact hn rfl
      | cons a ps => simp at hl
  simp only [he,List.mem_reverse]
  constructor
  · rintro ⟨hn,hp⟩
    exact ⟨hn,fun w hw => hp (wordValue w) (List.mem_map.mpr ⟨w,hw,rfl⟩)⟩
  · rintro ⟨hn,hp⟩
    refine ⟨hn,?_⟩
    intro w hw
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
    exact hp a ha

theorem positive_weight_parser_exact (input : List Bool) :
    positiveWeightParserResult input=readPositiveIntegerWeights input := by
  obtain ⟨b,ps,rest,he⟩ := counted_parser_payload_shape input
  have hd := decode_payloads_code (payloadListCode ps).length ps (le_refl _)
  simp only [readPositiveIntegerWeights,←counted_parser_exact,countedParserResult,he,
    pairFst_pair,pairSnd_pair,hd,positiveWeightParserResult,encodedPositiveWeightParser,
    nonempty_positive_word_list_value,payload_positive_reverse]
  cases b <;> cases q : decide (ps ≠ [] ∧ ∀ w ∈ ps, 0 < wordValue w)
  all_goals
    simp only [q,andBit,caseBit₀,Bool.cond_true,Bool.cond_false,List.cons.injEq,
      and_true,Bool.false_eq_true,if_true,if_false,bind,Option.bind_some,Option.bind_none,
      payload_positive_reverse]
  all_goals first
    | have hp := of_decide_eq_true q
      exact (if_pos hp).symm
    | have hp := of_decide_eq_false q
      exact (if_neg hp).symm

theorem positive_weight_input_value (input : List Bool) :
    polynomialPositiveWeightInput input=
      [match readPositiveIntegerWeights input with | none => false | some (_,tail) => decide (tail=[])] := by
  obtain ⟨b,ps,rest,he⟩ := counted_parser_payload_shape input
  have hd := decode_payloads_code (payloadListCode ps).length ps (le_refl _)
  rw [←positive_weight_parser_exact]
  simp only [polynomialPositiveWeightInput,positiveWeightParserResult,encodedPositiveWeightParser,
    he,pairFst_pair,pairSnd_pair,nonempty_positive_word_list_value,hd]
  cases b <;> cases q : decide (ps ≠ [] ∧ ∀ w ∈ ps, 0 < wordValue w) <;>
    cases rest <;> simp [q,andBit,caseBit₀,nonemptyFlag,caseBit]

theorem positive_weight_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedPositiveWeightParser (v 0) := by
  have h := encoded_counted_natural_parser_cobham
  have ho := Cobham.fstBlockFn (Cobham.sndBlockFn h)
  have hp := Cobham.comp nonempty_positive_word_list_cobham fun _ : Fin 1 => ho
  exact (Cobham.comp₂ Cobham.pairing (Cobham.andFn (Cobham.fstBlockFn h) hp)
    (Cobham.sndBlockFn h)).of_eq fun _ => rfl

theorem positive_weight_parser_mem_fp : encodedPositiveWeightParser ∈ FP :=
  CobhamFP_subset_FP positive_weight_parser_cobham

theorem positive_weight_input_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialPositiveWeightInput (v 0) := by
  have h := positive_weight_parser_cobham
  have ht := Cobham.sndBlockFn (Cobham.sndBlockFn h)
  exact (Cobham.andFn (Cobham.fstBlockFn h)
    (Cobham.iteFn (Cobham.nonemptyFn ht) (Cobham.const [false]) (Cobham.const [true]))).of_eq fun _ => rfl

theorem positive_weight_input_mem_fp : polynomialPositiveWeightInput ∈ FP :=
  CobhamFP_subset_FP positive_weight_input_cobham

theorem positive_weight_parser_actual_polytime : encodedPositiveWeightParser ∈ FP ∧
    ∀ input, positiveWeightParserResult input=readPositiveIntegerWeights input :=
  ⟨positive_weight_parser_mem_fp,positive_weight_parser_exact⟩

theorem positive_weight_parser_actual_input (P : IV04.Paper.IntegerPartition) (tail : List Bool) :
    positiveWeightParserResult (P.inputCode ++ tail)=some (P.weightList,tail) := by
  rw [positive_weight_parser_exact]
  have hn : P.weightList ≠ [] := by
    intro h
    have hl := P.weight_list_length
    rw [h] at hl
    have hp := P.nonempty
    simp at hl
    omega
  simp only [readPositiveIntegerWeights,P.read_actual_input,Option.bind_some]
  exact if_pos ⟨hn,P.weight_list_positive⟩

theorem positive_weight_input_actual_input (P : IV04.Paper.IntegerPartition) :
    polynomialPositiveWeightInput P.inputCode=[true] := by
  rw [positive_weight_input_value,←positive_weight_parser_exact]
  have he := positive_weight_parser_actual_input P []
  have he' : positiveWeightParserResult P.inputCode=some (P.weightList,[]) := by
    simpa only [List.append_nil] using he
  rw [he']
  rfl

#print axioms positive_weight_parser_actual_polytime
end IV04.Paper.Computational
