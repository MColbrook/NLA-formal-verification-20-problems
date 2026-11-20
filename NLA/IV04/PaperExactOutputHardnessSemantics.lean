module

public import NLA.IV04.PaperExactOutputHardnessPoly
public import NLA.IV04.PaperHullReductionHardness
public import NLA.IV04.PaperRealIntervalExtrema
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity SATReduction

theorem rational_parser_success_value_tail (input : List Bool) (q : ℚ) (tail : List Bool)
    (h : IV04.Paper.readRational input = some (q,tail)) :
    fractionWordValue (rationalParserFraction input) = q ∧
      pairSnd (pairSnd (encodedRationalParser input)) = tail := by
  have he := rational_parser_exact input
  by_cases hf : pairFst (encodedRationalParser input) = [true]
  · rw [if_pos hf,h] at he
    have hv := Option.some.inj he
    exact ⟨by simpa only [rational_parser_fraction] using congrArg Prod.fst hv,
      congrArg Prod.snd hv⟩
  · rw [if_neg hf,h] at he
    cases he

theorem polynomial_partition_output_query_read (P : IV04.Paper.IntegerPartition) (tail : List Bool) :
    readMatrixRationals (polynomialPartitionOutputQuery P.inputCode ++ tail) =
      some (P.layerCount,(partitionMatrixEndpointPairs P).flatMap (fun row => [row.1,row.2]) ++ [0],tail) := by
  simp only [polynomialPartitionOutputQuery,partition_layer_count_word,canonical_word_code_exact,
    partition_bits_value,List.append_assoc,readMatrixRationals,IV04.Paper.read_natural_code,
    bind,Option.bind_some]
  rw [read_rationals_append,polynomial_partition_table_read]
  simp only [bind,Option.bind_some,readRationals,IV04.Paper.read_rational_code,Option.pure_def]

theorem polynomial_partition_output_query_identifies (P : IV04.Paper.IntegerPartition)
    (n : ℕ) (pairs : List (ℚ × ℚ))
    (hr : readMatrixRationals (polynomialPartitionOutputQuery P.inputCode) =
      some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [0],[]))
    (hlen : pairs.length = n*n) : n = P.layerCount ∧ pairs = partitionMatrixEndpointPairs P := by
  have hread := polynomial_partition_output_query_read P []
  simp only [List.append_nil] at hread
  have he := Option.some.inj (hr.symm.trans hread)
  have hn : n = P.layerCount := congrArg Prod.fst he
  subst n
  have hv : pairs.flatMap (fun row => [row.1,row.2]) ++ [0] =
      (partitionMatrixEndpointPairs P).flatMap (fun row => [row.1,row.2]) ++ [0] :=
    congrArg (fun z : ℕ × List ℚ × List Bool => z.2.1) he
  have hp := (rational_pair_fields_threshold_injective pairs (partitionMatrixEndpointPairs P)
    0 0 (hlen.trans (partition_endpoint_pairs_length P).symm) hv).1
  exact ⟨rfl,hp⟩

#print axioms rational_parser_success_value_tail
#print axioms polynomial_partition_output_query_read
#print axioms polynomial_partition_output_query_identifies
end IV04.Paper.Computational
