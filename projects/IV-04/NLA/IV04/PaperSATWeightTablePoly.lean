module

public import NLA.IV04.PaperSATWeightTableDefinitions
public import NLA.IV04.PaperBoundedPayloadMapPoly
public import NLA.IV04.PaperSATRemainingWeightsPoly
public import NLA.IV04.PaperWordSubtractionPoly
public import NLA.IV04.PaperSubsetPartitionBuilderPoly
public import NLA.IV04.PaperPayloadReversePoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational
 theorem polynomial_sat_table_metadata_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATTableMetadata (v 0) := by
  unfold polynomialSATTableMetadata
  exact sat_literal_cobham_unary polynomialSATMetadata polynomial_sat_metadata_cobham _
    (sat_literal_cobham_snd _ polynomial_sat_cnf_parse_cobham)
 theorem polynomial_sat_slack_copies_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATSlackCopies (v 0) := by
  have hv := sat_literal_cobham_fst _ polynomial_sat_table_metadata_cobham
  have hl := sat_literal_cobham_snd _ (sat_literal_cobham_snd _ polynomial_sat_table_metadata_cobham)
  have ht := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham _ _ hv hl
  have hs := sat_literal_cobham_binary polynomialWordSub polynomial_word_sub_cobham
    _ (fun _ : Fin 1 → List Bool => [true]) ht (.const [true])
  unfold polynomialSATSlackCopies
  exact sat_literal_cobham_unary canonicalWord canonical_word_cobham _ hs
 theorem polynomial_sat_table_count_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATTableCount (v 0) := by
  have hv := sat_literal_cobham_fst _ polynomial_sat_table_metadata_cobham
  have hm := sat_literal_cobham_fst _ (sat_literal_cobham_snd _ polynomial_sat_table_metadata_cobham)
  have ht := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham
    _ (fun _ : Fin 1 → List Bool => [false,true]) hv (.const [false,true])
  have hs := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham
    _ (fun v : Fin 1 → List Bool => polynomialSATSlackCopies (v 0)) hm polynomial_sat_slack_copies_cobham
  have ha := sat_literal_cobham_binary polynomialWordAdd polynomial_word_add_cobham _ _ ht hs
  unfold polynomialSATTableCount
  exact sat_literal_cobham_unary canonicalWord canonical_word_cobham _ ha
 theorem polynomial_sat_literal_chunk_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATLiteralChunk (v 0) := by
  have hb := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hi := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hqt := sat_literal_cobham_binary pair Cobham.pairing
    (fun v : Fin 1 → List Bool => pairFst (v 0))
    (fun v : Fin 1 → List Bool => pair (pairSnd (v 0)) [true]) hb
    (sat_literal_cobham_binary pair Cobham.pairing _ (fun _ : Fin 1 → List Bool => [true]) hi (.const [true]))
  have hqf := sat_literal_cobham_binary pair Cobham.pairing
    (fun v : Fin 1 → List Bool => pairFst (v 0))
    (fun v : Fin 1 → List Bool => pair (pairSnd (v 0)) [false]) hb
    (sat_literal_cobham_binary pair Cobham.pairing _ (fun _ : Fin 1 → List Bool => [false]) hi (.const [false]))
  have ht := sat_literal_cobham_unary polynomialSATLiteralWeight polynomial_sat_literal_weight_cobham _ hqt
  have hf := sat_literal_cobham_unary polynomialSATLiteralWeight polynomial_sat_literal_weight_cobham _ hqf
  unfold polynomialSATLiteralChunk
  exact sat_literal_cobham_binary pair Cobham.pairing _ _ ht
    (sat_literal_cobham_binary pair Cobham.pairing _ (fun _ : Fin 1 → List Bool => []) hf (.const []))
 theorem polynomial_sat_slack_chunk_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATSlackChunk (v 0) := by
  have hb := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => v 0) (.proj 0)
  have hp := sat_literal_cobham_unary (fun bits => false::bits) (Cobham.bit false) _ hb
  have hr := sat_literal_cobham_binary smash Cobham.smash _ _ hp hp
  have hc := sat_literal_cobham_unary polynomialSATSlackCopies polynomial_sat_slack_copies_cobham _ hb
  have harg := sat_literal_cobham_binary pair Cobham.pairing _ _ hr
    (sat_literal_cobham_binary pair Cobham.pairing _ _ hc polynomial_sat_slack_weight_cobham)
  unfold polynomialSATSlackChunk
  exact sat_literal_cobham_unary polynomialBoundedPayloadRepeat
    (FP_subset_CobhamFP polynomial_bounded_payload_repeat_mem_fp) _ harg
 theorem polynomial_sat_reversed_weights_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATReversedWeights (v 0) := by
  have hv := sat_literal_cobham_fst _ polynomial_sat_table_metadata_cobham
  have hm := sat_literal_cobham_fst _ (sat_literal_cobham_snd _ polynomial_sat_table_metadata_cobham)
  have hav := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => v 0)
    (fun v : Fin 1 → List Bool => pair (pairFst (polynomialSATTableMetadata (v 0))) (v 0)) (.proj 0)
    (sat_literal_cobham_binary pair Cobham.pairing _ (fun v : Fin 1 → List Bool => v 0) hv (.proj 0))
  have ham := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => v 0)
    (fun v : Fin 1 → List Bool => pair (pairFst (pairSnd (polynomialSATTableMetadata (v 0)))) (v 0)) (.proj 0)
    (sat_literal_cobham_binary pair Cobham.pairing _ (fun v : Fin 1 → List Bool => v 0) hm (.proj 0))
  have hf := sat_literal_cobham_unary (polynomialBoundedPayloadMap polynomialSATLiteralChunk)
    (FP_subset_CobhamFP (polynomial_bounded_payload_map_mem_fp polynomialSATLiteralChunk
      (CobhamFP_subset_FP polynomial_sat_literal_chunk_cobham))) _ hav
  have hs := sat_literal_cobham_unary (polynomialBoundedPayloadMap polynomialSATSlackChunk)
    (FP_subset_CobhamFP (polynomial_bounded_payload_map_mem_fp polynomialSATSlackChunk
      (CobhamFP_subset_FP polynomial_sat_slack_chunk_cobham))) _ ham
  unfold polynomialSATReversedWeights
  exact Cobham.appendFn hs hf
 theorem polynomial_sat_weight_table_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATWeightTable (v 0) := by
  unfold polynomialSATWeightTable
  exact sat_literal_cobham_unary polynomialPayloadReverse polynomial_payload_reverse_cobham _
    polynomial_sat_reversed_weights_cobham
 theorem polynomial_sat_subset_input_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSATSubsetInput (v 0) := by
  unfold polynomialSATSubsetInput
  exact sat_literal_cobham_binary pair Cobham.pairing _ _ polynomial_sat_table_count_cobham
    (sat_literal_cobham_binary pair Cobham.pairing _ _ polynomial_sat_target_weight_cobham
      polynomial_sat_weight_table_cobham)
 theorem polynomial_sat_partition_code_mem_fp : polynomialSATPartitionCode ∈ FP := by
  have hg := sat_literal_cobham_fst _ polynomial_sat_cnf_parse_cobham
  have hb := sat_literal_cobham_unary polynomialSubsetPartitionCode subset_partition_builder_cobham _
    polynomial_sat_subset_input_cobham
  exact CobhamFP_subset_FP ((Cobham.iteFn hg hb
    (.const (SATReduction.countedWeightCode 2 ![1,2]))).of_eq fun _ => rfl)
#print axioms polynomial_sat_partition_code_mem_fp
end IV04.Paper.Computational
