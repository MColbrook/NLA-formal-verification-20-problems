module

public import NLA.IV04.PaperPartitionScalarPoly
public import NLA.IV04.PaperMatrixCoefficientInputSemantics
public import NLA.IV04.PaperWordListSumSemantics
public import NLA.IV04.PaperBinaryFractions
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem polynomial_partition_count_value (P : IV04.Paper.IntegerPartition) :
    wordValue (polynomialPartitionCount P.inputCode) = P.m := by
  obtain ⟨payload,hp,hv⟩ := natural_parser_success_shape P.inputCode P.m
    (P.weightList.flatMap IV04.Paper.naturalCode)
    (by simp [IV04.Paper.IntegerPartition.inputCode,IV04.Paper.read_natural_code])
  simp only [polynomialPartitionCount,hp,pairFst_pair,pairSnd_pair,canonical_word_value,hv]

theorem polynomial_partition_layer_count_value (P : IV04.Paper.IntegerPartition) :
    wordValue (polynomialPartitionLayerCount P.inputCode) = P.layerCount := by
  simp [polynomialPartitionLayerCount,canonical_word_value,polynomial_word_sub_value,
    wordValue,bitValue,polynomial_partition_count_value,IV04.Paper.IntegerPartition.layerCount]
  omega

theorem polynomial_partition_scale_value (P : IV04.Paper.IntegerPartition) :
    wordValue (polynomialPartitionScale P.inputCode) = P.denominatorScale := by
  simp [polynomialPartitionScale,canonical_word_multiply_value,parsed_weight_total_actual_input,
    wordValue,bitValue,IV04.Paper.IntegerPartition.denominatorScale,pow_two]

theorem polynomial_partition_squared_scale_value (P : IV04.Paper.IntegerPartition) :
    wordValue (polynomialPartitionSquaredScale P.inputCode) = P.squaredScale := by
  simp [polynomialPartitionSquaredScale,canonical_word_multiply_value,
    polynomial_partition_scale_value,IV04.Paper.IntegerPartition.squaredScale,pow_two]

#print axioms polynomial_partition_count_value
#print axioms polynomial_partition_layer_count_value
#print axioms polynomial_partition_scale_value
#print axioms polynomial_partition_squared_scale_value
end IV04.Paper.Computational
