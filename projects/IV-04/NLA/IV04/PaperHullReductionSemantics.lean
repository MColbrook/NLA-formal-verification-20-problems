module

public import NLA.IV04.PaperHullReductionPoly
public import NLA.IV04.PaperPartitionMatrixOutputSemantics
public import NLA.IV04.PaperConstructedHull
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem polynomial_partition_hull_threshold_value (P : IV04.Paper.IntegerPartition) :
    fractionWordValue (polynomialPartitionHullThresholdFraction P.inputCode) = 1/P.threshold := by
  have hs : 0 < P.denominatorScale := by
    dsimp [IV04.Paper.IntegerPartition.denominatorScale]
    have := P.total_pos
    positivity
  have hq : 0 < P.squaredScale := by
    dsimp [IV04.Paper.IntegerPartition.squaredScale]
    positivity
  have hle : 1 ≤ 2*P.squaredScale := by omega
  rw [P.threshold_scaled_fraction]
  simp [polynomialPartitionHullThresholdFraction,fractionWordValue,signedWordValue,firstBit,
    polynomial_word_sub_value,wordValue,bitValue,polynomial_partition_squared_scale_value,
    Nat.cast_sub hle,one_div,inv_div]

theorem polynomial_partition_hull_code_read (P : IV04.Paper.IntegerPartition) (tail : List Bool) :
    readMatrixRationals (polynomialPartitionHullCode P.inputCode ++ tail) =
      some (P.layerCount,(partitionMatrixEndpointPairs P).flatMap (fun row => [row.1,row.2]) ++ [1/P.threshold],tail) := by
  simp only [polynomialPartitionHullCode,partition_layer_count_word,canonical_word_code_exact,
    partition_bits_value,List.append_assoc,readMatrixRationals,IV04.Paper.read_natural_code,
    bind,Option.bind_some]
  rw [read_rationals_append,polynomial_partition_table_read]
  simp only [bind,Option.bind_some,readRationals,polynomial_fraction_output_read,
    polynomial_partition_hull_threshold_value,Option.pure_def]

#print axioms polynomial_partition_hull_threshold_value
#print axioms polynomial_partition_hull_code_read
end IV04.Paper.Computational
