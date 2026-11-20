module

public import NLA.IV04.PaperPartitionMatrixDefinitions
public import NLA.IV04.PaperPartitionScalarPoly
public import NLA.IV04.PaperFractionOutputPoly
public import NLA.IV04.PaperBoundedPayloadMapPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
open Complexity.Cobham

theorem polynomial_partition_word_equal_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionWordEqual (v 0) := by
  have h0 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h2 := sat_literal_cobham_binary polynomialWordLe polynomial_word_le_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h0 h1
  have h3 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h4 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h5 := sat_literal_cobham_binary polynomialWordLe polynomial_word_le_cobham (fun v : Fin 1 → List Bool => (pairSnd (v 0))) (fun v : Fin 1 → List Bool => (pairFst (v 0))) h3 h4
  have h6 := Cobham.andFn h2 h5
  unfold polynomialPartitionWordEqual
  exact h6
theorem polynomial_partition_word_equal_mem_fp : polynomialPartitionWordEqual ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_word_equal_cobham
#print axioms polynomial_partition_word_equal_mem_fp

theorem polynomial_partition_mod_zero_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionModZero (v 0) := by
  have h0 := Cobham.headFlagFn (Cobham.proj (0 : Fin 1))
  have h1 := Cobham.notFn h0
  have h2 := Cobham.tailFn (Cobham.proj (0 : Fin 1))
  have h3 := Cobham.headFlagFn h2
  have h4 := Cobham.notFn h3
  have h5 := Cobham.andFn h1 h4
  unfold polynomialPartitionModZero
  exact h5
theorem polynomial_partition_mod_zero_mem_fp : polynomialPartitionModZero ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_mod_zero_cobham
#print axioms polynomial_partition_mod_zero_mem_fp

theorem polynomial_partition_mod_one_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionModOne (v 0) := by
  have h0 := Cobham.headFlagFn (Cobham.proj (0 : Fin 1))
  have h1 := Cobham.tailFn (Cobham.proj (0 : Fin 1))
  have h2 := Cobham.headFlagFn h1
  have h3 := Cobham.notFn h2
  have h4 := Cobham.andFn h0 h3
  unfold polynomialPartitionModOne
  exact h4
theorem polynomial_partition_mod_one_mem_fp : polynomialPartitionModOne ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_mod_one_cobham
#print axioms polynomial_partition_mod_one_mem_fp

theorem polynomial_partition_mod_two_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionModTwo (v 0) := by
  have h0 := Cobham.headFlagFn (Cobham.proj (0 : Fin 1))
  have h1 := Cobham.notFn h0
  have h2 := Cobham.tailFn (Cobham.proj (0 : Fin 1))
  have h3 := Cobham.headFlagFn h2
  have h4 := Cobham.andFn h1 h3
  unfold polynomialPartitionModTwo
  exact h4
theorem polynomial_partition_mod_two_mem_fp : polynomialPartitionModTwo ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_mod_two_cobham
#print axioms polynomial_partition_mod_two_mem_fp

theorem polynomial_partition_quarter_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionQuarter (v 0) := by
  have h0 := Cobham.tailFn (Cobham.proj (0 : Fin 1))
  have h1 := Cobham.tailFn h0
  have h2 := sat_literal_cobham_unary canonicalWord canonical_word_cobham (fun v : Fin 1 → List Bool => (((v 0)).tail).tail) h1
  unfold polynomialPartitionQuarter
  exact h2
theorem polynomial_partition_quarter_mem_fp : polynomialPartitionQuarter ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_quarter_cobham
#print axioms polynomial_partition_quarter_mem_fp

theorem polynomial_partition_reverse_index_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionReverseIndex (v 0) := by
  have h0 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_binary polynomialWordSub polynomial_word_sub_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) (fun v : Fin 1 → List Bool => ([true])) h0 (.const ([true]))
  have h2 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h3 := sat_literal_cobham_binary polynomialWordSub polynomial_word_sub_cobham (fun v : Fin 1 → List Bool => (polynomialWordSub (pairFst (v 0)) ([true]))) (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h1 h2
  have h4 := sat_literal_cobham_unary canonicalWord canonical_word_cobham (fun v : Fin 1 → List Bool => (polynomialWordSub (polynomialWordSub (pairFst (v 0)) ([true])) (pairSnd (v 0)))) h3
  unfold polynomialPartitionReverseIndex
  exact h4
theorem polynomial_partition_reverse_index_mem_fp : polynomialPartitionReverseIndex ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_reverse_index_cobham
#print axioms polynomial_partition_reverse_index_mem_fp

theorem polynomial_partition_ruler_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionRuler (v 0) := by
  have h0 := sat_literal_cobham_unary (fun bits : List Bool => false :: bits) (Cobham.bit false) (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_binary smash Cobham.smash (fun v : Fin 1 → List Bool => (false :: (v 0))) (fun v : Fin 1 → List Bool => ([true,true,true,true])) h0 (.const ([true,true,true,true]))
  unfold polynomialPartitionRuler
  exact h1
theorem polynomial_partition_ruler_mem_fp : polynomialPartitionRuler ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_ruler_cobham
#print axioms polynomial_partition_ruler_mem_fp

theorem polynomial_partition_negative_cosine_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionNegativeCosine (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionMinus polynomial_partition_minus_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_unary (fun bits : List Bool => true :: bits) (Cobham.bit true) (fun v : Fin 1 → List Bool => (polynomialPartitionMinus (v 0))) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionPlus polynomial_partition_plus_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h3 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (true :: (polynomialPartitionMinus (v 0)))) (fun v : Fin 1 → List Bool => (polynomialPartitionPlus (v 0))) h1 h2
  unfold polynomialPartitionNegativeCosine
  exact h3
theorem polynomial_partition_negative_cosine_mem_fp : polynomialPartitionNegativeCosine ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_negative_cosine_cobham
#print axioms polynomial_partition_negative_cosine_mem_fp

theorem polynomial_partition_lower_fraction_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionLowerFraction (v 0) := by
  have h0 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h0
  have h2 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h3 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h2
  have h4 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) (fun v : Fin 1 → List Bool => (pairSnd (pairSnd (v 0)))) h1 h3
  have h5 := sat_literal_cobham_unary polynomialPartitionWordEqual polynomial_partition_word_equal_cobham (fun v : Fin 1 → List Bool => (pair (pairFst (pairSnd (v 0))) (pairSnd (pairSnd (v 0))))) h4
  have h6 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h7 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h6
  have h8 := sat_literal_cobham_unary polynomialPartitionModZero polynomial_partition_mod_zero_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) h7
  have h9 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h10 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h11 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h10
  have h12 := sat_literal_cobham_unary polynomialPartitionQuarter polynomial_partition_quarter_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) h11
  have h13 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairFst (v 0))) (fun v : Fin 1 → List Bool => (polynomialPartitionQuarter (pairFst (pairSnd (v 0))))) h9 h12
  have h14 := sat_literal_cobham_unary polynomialPartitionSineFraction polynomial_partition_sine_fraction_cobham (fun v : Fin 1 → List Bool => (pair (pairFst (v 0)) (polynomialPartitionQuarter (pairFst (pairSnd (v 0)))))) h13
  have h15 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h16 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h15
  have h17 := sat_literal_cobham_unary polynomialPartitionModOne polynomial_partition_mod_one_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) h16
  have h18 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h19 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h20 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h19
  have h21 := sat_literal_cobham_unary polynomialPartitionQuarter polynomial_partition_quarter_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) h20
  have h22 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairFst (v 0))) (fun v : Fin 1 → List Bool => (polynomialPartitionQuarter (pairFst (pairSnd (v 0))))) h18 h21
  have h23 := sat_literal_cobham_unary polynomialPartitionCompanionDiagonal polynomial_partition_companion_diagonal_cobham (fun v : Fin 1 → List Bool => (pair (pairFst (v 0)) (polynomialPartitionQuarter (pairFst (pairSnd (v 0)))))) h22
  have h24 := Cobham.iteFn h17 h23 (.const (pair [false] [true]))
  have h25 := Cobham.iteFn h8 h14 h24
  have h26 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h27 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h26
  have h28 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h29 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h28
  have h30 := sat_literal_cobham_binary polynomialWordAdd polynomial_word_add_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) (fun v : Fin 1 → List Bool => ([true])) h29 (.const ([true]))
  have h31 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairSnd (pairSnd (v 0)))) (fun v : Fin 1 → List Bool => (polynomialWordAdd (pairFst (pairSnd (v 0))) ([true]))) h27 h30
  have h32 := sat_literal_cobham_unary polynomialPartitionWordEqual polynomial_partition_word_equal_cobham (fun v : Fin 1 → List Bool => (pair (pairSnd (pairSnd (v 0))) (polynomialWordAdd (pairFst (pairSnd (v 0))) ([true])))) h31
  have h33 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h34 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h33
  have h35 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h36 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h35
  have h37 := sat_literal_cobham_binary polynomialWordAdd polynomial_word_add_cobham (fun v : Fin 1 → List Bool => (pairSnd (pairSnd (v 0)))) (fun v : Fin 1 → List Bool => ([true])) h36 (.const ([true]))
  have h38 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) (fun v : Fin 1 → List Bool => (polynomialWordAdd (pairSnd (pairSnd (v 0))) ([true]))) h34 h37
  have h39 := sat_literal_cobham_unary polynomialPartitionWordEqual polynomial_partition_word_equal_cobham (fun v : Fin 1 → List Bool => (pair (pairFst (pairSnd (v 0))) (polynomialWordAdd (pairSnd (pairSnd (v 0))) ([true])))) h38
  have h40 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h41 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h40
  have h42 := sat_literal_cobham_unary polynomialPartitionModZero polynomial_partition_mod_zero_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) h41
  have h43 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h44 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h45 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h44
  have h46 := sat_literal_cobham_unary polynomialPartitionQuarter polynomial_partition_quarter_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) h45
  have h47 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairFst (v 0))) (fun v : Fin 1 → List Bool => (polynomialPartitionQuarter (pairFst (pairSnd (v 0))))) h43 h46
  have h48 := sat_literal_cobham_unary polynomialPartitionNegativeCosine polynomial_partition_negative_cosine_cobham (fun v : Fin 1 → List Bool => (pair (pairFst (v 0)) (polynomialPartitionQuarter (pairFst (pairSnd (v 0)))))) h47
  have h49 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h50 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h49
  have h51 := sat_literal_cobham_unary polynomialPartitionModOne polynomial_partition_mod_one_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) h50
  have h52 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h53 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h54 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h53
  have h55 := sat_literal_cobham_unary polynomialPartitionQuarter polynomial_partition_quarter_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) h54
  have h56 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairFst (v 0))) (fun v : Fin 1 → List Bool => (polynomialPartitionQuarter (pairFst (pairSnd (v 0))))) h52 h55
  have h57 := sat_literal_cobham_unary polynomialPartitionCompanionBeta polynomial_partition_companion_beta_cobham (fun v : Fin 1 → List Bool => (pair (pairFst (v 0)) (polynomialPartitionQuarter (pairFst (pairSnd (v 0)))))) h56
  have h58 := Cobham.iteFn h51 h57 (.const (pair [true,true] [true]))
  have h59 := Cobham.iteFn h42 h48 h58
  have h60 := Cobham.iteFn h39 h59 (.const (pair [false] [true]))
  have h61 := Cobham.iteFn h32 (.const (pair [false,true] [true])) h60
  have h62 := Cobham.iteFn h5 h25 h61
  unfold polynomialPartitionLowerFraction
  exact h62
theorem polynomial_partition_lower_fraction_mem_fp : polynomialPartitionLowerFraction ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_lower_fraction_cobham
#print axioms polynomial_partition_lower_fraction_mem_fp

theorem polynomial_partition_upper_fraction_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionUpperFraction (v 0) := by
  have h0 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h0
  have h2 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h3 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h2
  have h4 := sat_literal_cobham_binary polynomialWordAdd polynomial_word_add_cobham (fun v : Fin 1 → List Bool => (pairSnd (pairSnd (v 0)))) (fun v : Fin 1 → List Bool => ([true])) h3 (.const ([true]))
  have h5 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) (fun v : Fin 1 → List Bool => (polynomialWordAdd (pairSnd (pairSnd (v 0))) ([true]))) h1 h4
  have h6 := sat_literal_cobham_unary polynomialPartitionWordEqual polynomial_partition_word_equal_cobham (fun v : Fin 1 → List Bool => (pair (pairFst (pairSnd (v 0))) (polynomialWordAdd (pairSnd (pairSnd (v 0))) ([true])))) h5
  have h7 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h8 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h7
  have h9 := sat_literal_cobham_unary polynomialPartitionModTwo polynomial_partition_mod_two_cobham (fun v : Fin 1 → List Bool => (pairFst (pairSnd (v 0)))) h8
  have h10 := Cobham.andFn h6 h9
  have h11 := sat_literal_cobham_unary polynomialPartitionLowerFraction polynomial_partition_lower_fraction_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h12 := Cobham.iteFn h10 (.const (pair [false,true] [true])) h11
  unfold polynomialPartitionUpperFraction
  exact h12
theorem polynomial_partition_upper_fraction_mem_fp : polynomialPartitionUpperFraction ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_upper_fraction_cobham
#print axioms polynomial_partition_upper_fraction_mem_fp

theorem polynomial_partition_endpoint_fields_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionEndpointFields (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionLowerFraction polynomial_partition_lower_fraction_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_unary polynomialFractionOutput polynomial_fraction_output_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionLowerFraction (v 0))) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionUpperFraction polynomial_partition_upper_fraction_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h3 := sat_literal_cobham_unary polynomialFractionOutput polynomial_fraction_output_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionUpperFraction (v 0))) h2
  have h4 := Cobham.appendFn h1 h3
  unfold polynomialPartitionEndpointFields
  exact h4
theorem polynomial_partition_endpoint_fields_mem_fp : polynomialPartitionEndpointFields ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_endpoint_fields_cobham
#print axioms polynomial_partition_endpoint_fields_mem_fp

theorem polynomial_partition_column_chunk_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionColumnChunk (v 0) := by
  have h0 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairFst (v 0))) h0
  have h2 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h3 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (pairFst (v 0))) h2
  have h4 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h5 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (pairFst (v 0))) h4
  have h6 := sat_literal_cobham_unary polynomialPartitionLayerCount polynomial_partition_layer_count_cobham (fun v : Fin 1 → List Bool => (pairFst (pairFst (v 0)))) h5
  have h7 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h8 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (polynomialPartitionLayerCount (pairFst (pairFst (v 0))))) (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h6 h7
  have h9 := sat_literal_cobham_unary polynomialPartitionReverseIndex polynomial_partition_reverse_index_cobham (fun v : Fin 1 → List Bool => (pair (polynomialPartitionLayerCount (pairFst (pairFst (v 0)))) (pairSnd (v 0)))) h8
  have h10 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairSnd (pairFst (v 0)))) (fun v : Fin 1 → List Bool => (polynomialPartitionReverseIndex (pair (polynomialPartitionLayerCount (pairFst (pairFst (v 0)))) (pairSnd (v 0))))) h3 h9
  have h11 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairFst (pairFst (v 0)))) (fun v : Fin 1 → List Bool => (pair (pairSnd (pairFst (v 0))) (polynomialPartitionReverseIndex (pair (polynomialPartitionLayerCount (pairFst (pairFst (v 0)))) (pairSnd (v 0)))))) h1 h10
  have h12 := sat_literal_cobham_unary polynomialPartitionEndpointFields polynomial_partition_endpoint_fields_cobham (fun v : Fin 1 → List Bool => (pair (pairFst (pairFst (v 0))) (pair (pairSnd (pairFst (v 0))) (polynomialPartitionReverseIndex (pair (polynomialPartitionLayerCount (pairFst (pairFst (v 0)))) (pairSnd (v 0))))))) h11
  unfold polynomialPartitionColumnChunk
  exact h12
theorem polynomial_partition_column_chunk_mem_fp : polynomialPartitionColumnChunk ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_column_chunk_cobham
#print axioms polynomial_partition_column_chunk_mem_fp

theorem polynomial_partition_row_chunk_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionRowChunk (v 0) := by
  have h0 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_unary polynomialPartitionRuler polynomial_partition_ruler_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) h0
  have h2 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h3 := sat_literal_cobham_unary polynomialPartitionLayerCount polynomial_partition_layer_count_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) h2
  have h4 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h5 := sat_literal_cobham_fst (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h6 := sat_literal_cobham_unary polynomialPartitionLayerCount polynomial_partition_layer_count_cobham (fun v : Fin 1 → List Bool => (pairFst (v 0))) h5
  have h7 := sat_literal_cobham_snd (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h8 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (polynomialPartitionLayerCount (pairFst (v 0)))) (fun v : Fin 1 → List Bool => (pairSnd (v 0))) h6 h7
  have h9 := sat_literal_cobham_unary polynomialPartitionReverseIndex polynomial_partition_reverse_index_cobham (fun v : Fin 1 → List Bool => (pair (polynomialPartitionLayerCount (pairFst (v 0))) (pairSnd (v 0)))) h8
  have h10 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (pairFst (v 0))) (fun v : Fin 1 → List Bool => (polynomialPartitionReverseIndex (pair (polynomialPartitionLayerCount (pairFst (v 0))) (pairSnd (v 0))))) h4 h9
  have h11 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (polynomialPartitionLayerCount (pairFst (v 0)))) (fun v : Fin 1 → List Bool => (pair (pairFst (v 0)) (polynomialPartitionReverseIndex (pair (polynomialPartitionLayerCount (pairFst (v 0))) (pairSnd (v 0)))))) h3 h10
  have h12 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (polynomialPartitionRuler (pairFst (v 0)))) (fun v : Fin 1 → List Bool => (pair (polynomialPartitionLayerCount (pairFst (v 0))) (pair (pairFst (v 0)) (polynomialPartitionReverseIndex (pair (polynomialPartitionLayerCount (pairFst (v 0))) (pairSnd (v 0))))))) h1 h11
  have h13 := sat_literal_cobham_unary (polynomialBoundedPayloadMap polynomialPartitionColumnChunk) (FP_subset_CobhamFP (polynomial_bounded_payload_map_mem_fp polynomialPartitionColumnChunk (CobhamFP_subset_FP polynomial_partition_column_chunk_cobham))) (fun v : Fin 1 → List Bool => (pair (polynomialPartitionRuler (pairFst (v 0))) (pair (polynomialPartitionLayerCount (pairFst (v 0))) (pair (pairFst (v 0)) (polynomialPartitionReverseIndex (pair (polynomialPartitionLayerCount (pairFst (v 0))) (pairSnd (v 0)))))))) h12
  unfold polynomialPartitionRowChunk
  exact h13
theorem polynomial_partition_row_chunk_mem_fp : polynomialPartitionRowChunk ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_row_chunk_cobham
#print axioms polynomial_partition_row_chunk_mem_fp

theorem polynomial_partition_endpoint_table_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionEndpointTable (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionRuler polynomial_partition_ruler_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_unary polynomialPartitionLayerCount polynomial_partition_layer_count_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h2 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (polynomialPartitionLayerCount (v 0))) (fun v : Fin 1 → List Bool => (v 0)) h1 (Cobham.proj (0 : Fin 1))
  have h3 := sat_literal_cobham_binary pair Cobham.pairing (fun v : Fin 1 → List Bool => (polynomialPartitionRuler (v 0))) (fun v : Fin 1 → List Bool => (pair (polynomialPartitionLayerCount (v 0)) (v 0))) h0 h2
  have h4 := sat_literal_cobham_unary (polynomialBoundedPayloadMap polynomialPartitionRowChunk) (FP_subset_CobhamFP (polynomial_bounded_payload_map_mem_fp polynomialPartitionRowChunk (CobhamFP_subset_FP polynomial_partition_row_chunk_cobham))) (fun v : Fin 1 → List Bool => (pair (polynomialPartitionRuler (v 0)) (pair (polynomialPartitionLayerCount (v 0)) (v 0)))) h3
  unfold polynomialPartitionEndpointTable
  exact h4
theorem polynomial_partition_endpoint_table_mem_fp : polynomialPartitionEndpointTable ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_endpoint_table_cobham
#print axioms polynomial_partition_endpoint_table_mem_fp

theorem polynomial_partition_matrix_code_cobham : Cobham fun v : Fin 1 → List Bool => polynomialPartitionMatrixCode (v 0) := by
  have h0 := sat_literal_cobham_unary polynomialPartitionLayerCount polynomial_partition_layer_count_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h1 := sat_literal_cobham_unary canonicalWordCode canonical_word_code_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionLayerCount (v 0))) h0
  have h2 := sat_literal_cobham_unary polynomialPartitionEndpointTable polynomial_partition_endpoint_table_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h3 := Cobham.appendFn h1 h2
  have h4 := sat_literal_cobham_unary polynomialPartitionThresholdFraction polynomial_partition_threshold_fraction_cobham (fun v : Fin 1 → List Bool => (v 0)) (Cobham.proj (0 : Fin 1))
  have h5 := sat_literal_cobham_unary polynomialFractionOutput polynomial_fraction_output_cobham (fun v : Fin 1 → List Bool => (polynomialPartitionThresholdFraction (v 0))) h4
  have h6 := Cobham.appendFn h3 h5
  unfold polynomialPartitionMatrixCode
  exact h6
theorem polynomial_partition_matrix_code_mem_fp : polynomialPartitionMatrixCode ∈ FP :=
  CobhamFP_subset_FP polynomial_partition_matrix_code_cobham
#print axioms polynomial_partition_matrix_code_mem_fp
end IV04.Paper.Computational
