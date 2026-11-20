module

public import NLA.IV04.PaperWordListSumPoly
public import NLA.IV04.PaperWordListProductSemantics
public import NLA.IV04.PaperPositiveWeightParser
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem word_list_sum_iterate_nil (k : ℕ) (total : List Bool) :
    (wordListSumStep^[k]) (Complexity.pair [] total)=Complexity.pair [] total := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,word_list_sum_step_pair]; simp

theorem word_list_sum_iteration_value (k : ℕ) (payloads : List (List Bool)) (total : List Bool)
    (h : payloads.length ≤ k) :
    wordValue (Complexity.pairSnd ((wordListSumStep^[k])
      (Complexity.pair (payloadListCode payloads) total)))=
      wordValue total+(payloads.map wordValue).sum := by
  induction k generalizing payloads total with
  | zero =>
    have he : payloads=[] := by cases payloads <;> simp_all
    simp [he,payloadListCode]
  | succ k ih =>
    cases payloads with
    | nil => simp [payloadListCode,word_list_sum_iterate_nil]
    | cons payload payloads =>
      have ht : payloads.length ≤ k := by simp only [List.length_cons] at h; omega
      rw [Function.iterate_succ_apply,word_list_sum_step_pair]
      simp only [payloadListCode,payload_pair_ne_nil,if_false,Complexity.pairFst_pair,Complexity.pairSnd_pair]
      rw [ih payloads (polynomialWordAdd total payload) ht,polynomial_word_add_value]
      simp [Nat.add_assoc]

theorem polynomial_word_list_sum_value (payloads : List (List Bool)) :
    wordValue (polynomialWordListSum (payloadListCode payloads))=(payloads.map wordValue).sum := by
  have h := word_list_sum_iteration_value (payloadListCode payloads).length payloads []
    (payload_list_count_length payloads)
  simpa [polynomialWordListSum,wordListSumState,wordValue] using h

theorem word_list_sum_actual_polytime : polynomialWordListSum ∈ Complexity.FP ∧
    ∀ payloads, wordValue (polynomialWordListSum (payloadListCode payloads))=(payloads.map wordValue).sum :=
  ⟨polynomial_word_list_sum_mem_fp,polynomial_word_list_sum_value⟩

theorem parsed_weight_total_value (input : List Bool) (weights : List ℕ) (tail : List Bool)
    (h : IV04.Paper.readIntegerWeights input=some (weights,tail)) :
    wordValue (polynomialParsedWeightTotal input)=weights.sum := by
  obtain ⟨b,ps,rest,he⟩ := counted_parser_payload_shape input
  have hd := decode_payloads_code (payloadListCode ps).length ps (le_refl _)
  rw [←counted_parser_exact] at h
  simp only [countedParserResult,he,Complexity.pairFst_pair,Complexity.pairSnd_pair,hd] at h
  cases b with
  | false => simp at h
  | true =>
    have hl : (ps.map wordValue).reverse=weights := congrArg Prod.fst (Option.some.inj h)
    simp only [polynomialParsedWeightTotal,he,Complexity.pairFst_pair,Complexity.pairSnd_pair,
      polynomial_word_list_sum_value]
    rw [←hl,List.sum_reverse]

theorem parsed_weight_total_actual_input (P : IV04.Paper.IntegerPartition) :
    wordValue (polynomialParsedWeightTotal P.inputCode)=P.total := by
  have h := parsed_weight_total_value P.inputCode P.weightList []
    (by simpa only [List.append_nil] using P.read_actual_input [])
  simpa only [IV04.Paper.IntegerPartition.weightList,List.sum_ofFn,
    IV04.Paper.IntegerPartition.total] using h

theorem parsed_weight_total_actual_polytime : polynomialParsedWeightTotal ∈ Complexity.FP ∧
    ∀ P : IV04.Paper.IntegerPartition, wordValue (polynomialParsedWeightTotal P.inputCode)=P.total :=
  ⟨parsed_weight_total_mem_fp,parsed_weight_total_actual_input⟩

#print axioms parsed_weight_total_actual_polytime
end IV04.Paper.Computational
