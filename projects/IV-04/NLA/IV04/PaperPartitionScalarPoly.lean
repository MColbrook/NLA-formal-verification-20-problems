module

public import NLA.IV04.PaperPartitionScalarDefinitions
public import NLA.IV04.PaperSATLiteralDigitsPoly
public import NLA.IV04.PaperWordListSumPoly
public import NLA.IV04.PaperPayloadLookupPoly
public import NLA.IV04.PaperWordSubtractionPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
open Complexity.Cobham

theorem polynomial_partition_count_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionCount (v 0) := by
  have h0 := sat_literal_cobham_unary encodedNaturalParser encoded_natural_parser_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (encodedNaturalParser (v 0))) h0
  have h2 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (encodedNaturalParser (v 0)))) h1
  have h3 := sat_literal_cobham_unary canonicalWord canonical_word_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (encodedNaturalParser (v 0))))) h2
  unfold polynomialPartitionCount
  exact h3
theorem polynomial_partition_count_mem_fp : polynomialPartitionCount ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_count_cobham
#print axioms polynomial_partition_count_mem_fp

theorem polynomial_partition_layer_count_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionLayerCount (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionCount polynomial_partition_count_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false) (fun v : Fin 1 → List Bool => (polynomialPartitionCount (v 0))) h0
  have h2 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false) (fun v : Fin 1 → List Bool => (false :: (polynomialPartitionCount (v 0)))) h1
  have h3 := sat_literal_cobham_binary polynomialWordSub polynomial_word_sub_cobham (fun v : Fin 1 → List Bool => (false :: (false :: (polynomialPartitionCount (v 0))))) (fun v : Fin 1 → List Bool => [false,true]) h2 (.const [false,true])
  have h4 := sat_literal_cobham_unary canonicalWord canonical_word_cobham (fun v : Fin 1 → List Bool => (polynomialWordSub (false :: (false :: (polynomialPartitionCount (v 0)))) [false,true])) h3
  unfold polynomialPartitionLayerCount
  exact h4
theorem polynomial_partition_layer_count_mem_fp : polynomialPartitionLayerCount ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_layer_count_cobham
#print axioms polynomial_partition_layer_count_mem_fp

theorem polynomial_partition_scale_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionScale (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialParsedWeightTotal parsed_weight_total_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary polynomialParsedWeightTotal parsed_weight_total_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h2 := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham (fun v : Fin 1 → List Bool => (polynomialParsedWeightTotal (v 0))) (fun v : Fin 1 → List Bool => (polynomialParsedWeightTotal (v 0))) h0 h1
  have h3 := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham (fun v : Fin 1 → List Bool => [false,true,false,true]) (fun v : Fin 1 → List Bool => (canonicalWordMultiply (polynomialParsedWeightTotal (v 0)) (polynomialParsedWeightTotal (v 0)))) (.const [false,true,false,true]) h2
  unfold polynomialPartitionScale
  exact h3
theorem polynomial_partition_scale_mem_fp : polynomialPartitionScale ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_scale_cobham
#print axioms polynomial_partition_scale_mem_fp

theorem polynomial_partition_squared_scale_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionSquaredScale (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionScale polynomial_partition_scale_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary polynomialPartitionScale polynomial_partition_scale_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h2 := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionScale (v 0))) (fun v : Fin 1 → List Bool => (polynomialPartitionScale (v 0))) h0 h1
  unfold polynomialPartitionSquaredScale
  exact h2
theorem polynomial_partition_squared_scale_mem_fp : polynomialPartitionSquaredScale ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_squared_scale_cobham
#print axioms polynomial_partition_squared_scale_mem_fp

theorem polynomial_partition_weight_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionWeight (v 0) := by
  have h0 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary polynomialPartitionCount polynomial_partition_count_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) h0
  have h2 := sat_literal_cobham_binary polynomialWordSub polynomial_word_sub_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionCount (pairFst (v 0)))) (fun v : Fin 1 → List Bool => [true]) h1 (.const [true])
  have h3 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h4 := sat_literal_cobham_binary polynomialWordSub polynomial_word_sub_cobham (fun v : Fin 1 → List Bool => (polynomialWordSub (polynomialPartitionCount (pairFst (v 0))) [true])) (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h2 h3
  have h5 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h6 := sat_literal_cobham_unary encodedCountedNaturalParser encoded_counted_natural_parser_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) h5
  have h7 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (encodedCountedNaturalParser (pairFst (v 0)))) h6
  have h8 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (encodedCountedNaturalParser (pairFst (v 0))))) h7
  have h9 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (polynomialWordSub (polynomialWordSub (polynomialPartitionCount (pairFst (v 0))) [true]) (pairSnd (v 0)))) (fun v : Fin 1 → List Bool => (pairFst (pairSnd (encodedCountedNaturalParser (pairFst (v 0)))))) h4 h8
  have h10 := sat_literal_cobham_unary polynomialPayloadLookup polynomial_payload_lookup_cobham (fun v : Fin 1 → List Bool => (pair (polynomialWordSub (polynomialWordSub (polynomialPartitionCount (pairFst (v 0))) [true]) (pairSnd (v 0))) (pairFst (pairSnd (encodedCountedNaturalParser (pairFst (v 0))))))) h9
  unfold polynomialPartitionWeight
  exact h10
theorem polynomial_partition_weight_mem_fp : polynomialPartitionWeight ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_weight_cobham
#print axioms polynomial_partition_weight_mem_fp

theorem polynomial_partition_plus_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionPlus (v 0) := by
  have h0 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary polynomialPartitionSquaredScale polynomial_partition_squared_scale_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionWeight polynomial_partition_weight_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h3 := sat_literal_cobham_unary polynomialPartitionWeight polynomial_partition_weight_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h4 := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionWeight (v 0))) (fun v : Fin 1 → List Bool => (polynomialPartitionWeight (v 0))) h2 h3
  have h5 := sat_literal_cobham_binary polynomialWordAdd polynomial_word_add_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionSquaredScale (pairFst (v 0)))) (fun v : Fin 1 → List Bool => (canonicalWordMultiply (polynomialPartitionWeight (v 0)) (polynomialPartitionWeight (v 0)))) h1 h4
  unfold polynomialPartitionPlus
  exact h5
theorem polynomial_partition_plus_mem_fp : polynomialPartitionPlus ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_plus_cobham
#print axioms polynomial_partition_plus_mem_fp

theorem polynomial_partition_minus_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionMinus (v 0) := by
  have h0 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary polynomialPartitionSquaredScale polynomial_partition_squared_scale_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionWeight polynomial_partition_weight_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h3 := sat_literal_cobham_unary polynomialPartitionWeight polynomial_partition_weight_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h4 := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionWeight (v 0))) (fun v : Fin 1 → List Bool => (polynomialPartitionWeight (v 0))) h2 h3
  have h5 := sat_literal_cobham_binary polynomialWordSub polynomial_word_sub_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionSquaredScale (pairFst (v 0)))) (fun v : Fin 1 → List Bool => (canonicalWordMultiply (polynomialPartitionWeight (v 0)) (polynomialPartitionWeight (v 0)))) h1 h4
  unfold polynomialPartitionMinus
  exact h5
theorem polynomial_partition_minus_mem_fp : polynomialPartitionMinus ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_minus_cobham
#print axioms polynomial_partition_minus_mem_fp

theorem polynomial_partition_sine_numerator_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionSineNumerator (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionWeight polynomial_partition_weight_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h2 := sat_literal_cobham_unary polynomialPartitionScale polynomial_partition_scale_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) h1
  have h3 := sat_literal_cobham_binary canonicalWordMultiply canonical_word_multiply_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionWeight (v 0))) (fun v : Fin 1 → List Bool => (polynomialPartitionScale (pairFst (v 0)))) h0 h2
  have h4 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false) (fun v : Fin 1 → List Bool => (canonicalWordMultiply (polynomialPartitionWeight (v 0)) (polynomialPartitionScale (pairFst (v 0))))) h3
  unfold polynomialPartitionSineNumerator
  exact h4
theorem polynomial_partition_sine_numerator_mem_fp : polynomialPartitionSineNumerator ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_sine_numerator_cobham
#print axioms polynomial_partition_sine_numerator_mem_fp

theorem polynomial_partition_sine_fraction_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionSineFraction (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionSineNumerator polynomial_partition_sine_numerator_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false) (fun v : Fin 1 → List Bool => (polynomialPartitionSineNumerator (v 0))) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionPlus polynomial_partition_plus_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h3 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (false :: (polynomialPartitionSineNumerator (v 0)))) (fun v : Fin 1 → List Bool => (polynomialPartitionPlus (v 0))) h1 h2
  unfold polynomialPartitionSineFraction
  exact h3
theorem polynomial_partition_sine_fraction_mem_fp : polynomialPartitionSineFraction ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_sine_fraction_cobham
#print axioms polynomial_partition_sine_fraction_mem_fp

theorem polynomial_partition_cosine_fraction_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionCosineFraction (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionMinus polynomial_partition_minus_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false) (fun v : Fin 1 → List Bool => (polynomialPartitionMinus (v 0))) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionPlus polynomial_partition_plus_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h3 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (false :: (polynomialPartitionMinus (v 0)))) (fun v : Fin 1 → List Bool => (polynomialPartitionPlus (v 0))) h1 h2
  unfold polynomialPartitionCosineFraction
  exact h3
theorem polynomial_partition_cosine_fraction_mem_fp : polynomialPartitionCosineFraction ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_cosine_fraction_cobham
#print axioms polynomial_partition_cosine_fraction_mem_fp

theorem polynomial_partition_companion_diagonal_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionCompanionDiagonal (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionSineNumerator polynomial_partition_sine_numerator_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary (fun bits : List Bool => true :: bits) (Cobham.bit true) (fun v : Fin 1 → List Bool => (polynomialPartitionSineNumerator (v 0))) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionMinus polynomial_partition_minus_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h3 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (true :: (polynomialPartitionSineNumerator (v 0)))) (fun v : Fin 1 → List Bool => (polynomialPartitionMinus (v 0))) h1 h2
  unfold polynomialPartitionCompanionDiagonal
  exact h3
theorem polynomial_partition_companion_diagonal_mem_fp : polynomialPartitionCompanionDiagonal ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_companion_diagonal_cobham
#print axioms polynomial_partition_companion_diagonal_mem_fp

theorem polynomial_partition_companion_beta_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionCompanionBeta (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionPlus polynomial_partition_plus_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary (fun bits : List Bool => true :: bits) (Cobham.bit true) (fun v : Fin 1 → List Bool => (polynomialPartitionPlus (v 0))) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionMinus polynomial_partition_minus_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h3 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (true :: (polynomialPartitionPlus (v 0)))) (fun v : Fin 1 → List Bool => (polynomialPartitionMinus (v 0))) h1 h2
  unfold polynomialPartitionCompanionBeta
  exact h3
theorem polynomial_partition_companion_beta_mem_fp : polynomialPartitionCompanionBeta ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_companion_beta_cobham
#print axioms polynomial_partition_companion_beta_mem_fp

theorem polynomial_partition_threshold_fraction_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionThresholdFraction (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionSquaredScale polynomial_partition_squared_scale_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h1 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false) (fun v : Fin 1 → List Bool => (polynomialPartitionSquaredScale (v 0))) h0
  have h2 := sat_literal_cobham_binary polynomialWordSub polynomial_word_sub_cobham (fun v : Fin 1 → List Bool => (false :: (polynomialPartitionSquaredScale (v 0)))) (fun v : Fin 1 → List Bool => [true]) h1 (.const [true])
  have h3 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false) (fun v : Fin 1 → List Bool => (polynomialWordSub (false :: (polynomialPartitionSquaredScale (v 0))) [true])) h2
  have h4 := sat_literal_cobham_unary polynomialPartitionSquaredScale polynomial_partition_squared_scale_cobham (fun v : Fin 1 → List Bool => (v 0)) (.proj 0)
  have h5 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false) (fun v : Fin 1 → List Bool => (polynomialPartitionSquaredScale (v 0))) h4
  have h6 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (false :: (polynomialWordSub (false :: (polynomialPartitionSquaredScale (v 0))) [true]))) (fun v : Fin 1 → List Bool => (false :: (polynomialPartitionSquaredScale (v 0)))) h3 h5
  unfold polynomialPartitionThresholdFraction
  exact h6
theorem polynomial_partition_threshold_fraction_mem_fp : polynomialPartitionThresholdFraction ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_threshold_fraction_cobham
#print axioms polynomial_partition_threshold_fraction_mem_fp
end IV04.Paper.Computational
