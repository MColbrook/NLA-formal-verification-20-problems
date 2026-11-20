module

public import NLA.IV04.PaperPartitionScalarSemantics
public import NLA.IV04.PaperPayloadLookupSemantics
public import NLA.IV04.PaperPositiveWeightParser
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem counted_parser_actual_weight_payloads (P : IV04.Paper.IntegerPartition) :
    ∃ ps : List (List Bool),
      pairFst (pairSnd (encodedCountedNaturalParser P.inputCode)) = payloadListCode ps ∧
      ps.length = P.m ∧ (ps.map wordValue).reverse = P.weightList := by
  obtain ⟨b,ps,rest,he⟩ := counted_parser_payload_shape P.inputCode
  have hd := decode_payloads_code (payloadListCode ps).length ps (le_refl _)
  have hp : IV04.Paper.readIntegerWeights P.inputCode = some (P.weightList,[]) := by
    simpa only [List.append_nil] using P.read_actual_input []
  rw [← counted_parser_exact] at hp
  simp only [countedParserResult,he,pairFst_pair,pairSnd_pair,hd] at hp
  cases b with
  | false => simp at hp
  | true =>
    have hl : (ps.map wordValue).reverse = P.weightList := congrArg Prod.fst (Option.some.inj hp)
    have hlen : ps.length = P.m := by
      have hv := congrArg List.length hl
      simpa only [List.length_reverse,List.length_map,P.weight_list_length] using hv
    exact ⟨ps,by simp only [he,pairFst_pair,pairSnd_pair],hlen,hl⟩

theorem polynomial_partition_weight_value (P : IV04.Paper.IntegerPartition) (i : Fin P.m) :
    wordValue (polynomialPartitionWeight (pair P.inputCode i.val.bits)) = P.weight i := by
  obtain ⟨ps,hps,hlen,hl⟩ := counted_parser_actual_weight_payloads P
  let index := polynomialWordSub (polynomialWordSub (polynomialPartitionCount P.inputCode) [true]) i.val.bits
  have hbits : wordValue i.val.bits = i.val := by
    rw [word_value_foldr];exact IV04.Paper.bits_foldr i.val
  have hi : wordValue index = P.m - 1 - i.val := by
    simp [index,polynomial_word_sub_value,polynomial_partition_count_value,hbits,wordValue,bitValue]
  have hb : wordValue index < ps.length := by rw [hi,hlen];have := i.isLt;omega
  have hr : i.val < ((ps.map wordValue).reverse).length := by
    simpa only [List.length_reverse,List.length_map,hlen] using i.isLt
  have hv : ((ps.map wordValue).reverse)[i.val]'hr = P.weight i := by
    simp [hl,IV04.Paper.IntegerPartition.weightList]
  rw [List.getElem_reverse] at hv
  simp only [List.length_map,List.getElem_map] at hv
  unfold polynomialPartitionWeight
  simp only [pairFst_pair,pairSnd_pair,hps]
  change wordValue (polynomialPayloadLookup (pair index (payloadListCode ps))) = P.weight i
  rw [payload_lookup_word_code ps index hb]
  simpa only [hi,hlen] using hv

theorem polynomial_partition_plus_value (P : IV04.Paper.IntegerPartition) (i : Fin P.m) :
    wordValue (polynomialPartitionPlus (pair P.inputCode i.val.bits)) = P.squaredScale + (P.weight i)^2 := by
  simp [polynomialPartitionPlus,pairFst_pair,polynomial_word_add_value,
    canonical_word_multiply_value,polynomial_partition_weight_value,
    polynomial_partition_squared_scale_value,pow_two]

theorem polynomial_partition_minus_value (P : IV04.Paper.IntegerPartition) (i : Fin P.m) :
    wordValue (polynomialPartitionMinus (pair P.inputCode i.val.bits)) = P.squaredScale - (P.weight i)^2 := by
  simp [polynomialPartitionMinus,pairFst_pair,polynomial_word_sub_value,
    canonical_word_multiply_value,polynomial_partition_weight_value,
    polynomial_partition_squared_scale_value,pow_two]

theorem polynomial_partition_sine_numerator_value (P : IV04.Paper.IntegerPartition) (i : Fin P.m) :
    wordValue (polynomialPartitionSineNumerator (pair P.inputCode i.val.bits)) = 2*P.weight i*P.denominatorScale := by
  simp [polynomialPartitionSineNumerator,pairFst_pair,wordValue,bitValue,
    canonical_word_multiply_value,polynomial_partition_weight_value,polynomial_partition_scale_value]
  ring
#print axioms counted_parser_actual_weight_payloads
#print axioms polynomial_partition_weight_value
#print axioms polynomial_partition_plus_value
#print axioms polynomial_partition_minus_value
#print axioms polynomial_partition_sine_numerator_value
end IV04.Paper.Computational
