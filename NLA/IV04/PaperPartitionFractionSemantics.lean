module

public import NLA.IV04.PaperPartitionWeightSemantics
public import NLA.IV04.PaperFractionOutputSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem polynomial_partition_sine_fraction_value (P : IV04.Paper.IntegerPartition) (i : Fin P.m) :
    fractionWordValue (polynomialPartitionSineFraction (pair P.inputCode i.val.bits)) = P.s i := by
  rw [P.sine_scaled_fraction]
  simp [polynomialPartitionSineFraction,fractionWordValue,signedWordValue,firstBit,
    polynomial_partition_sine_numerator_value,polynomial_partition_plus_value]

theorem polynomial_partition_cosine_fraction_value (P : IV04.Paper.IntegerPartition) (i : Fin P.m) :
    fractionWordValue (polynomialPartitionCosineFraction (pair P.inputCode i.val.bits)) = P.c i := by
  have hle : (P.weight i)^2 ≤ P.squaredScale := Nat.le_of_lt (P.squared_weight_lt_scale i)
  rw [P.cosine_scaled_fraction]
  simp [polynomialPartitionCosineFraction,fractionWordValue,signedWordValue,firstBit,
    polynomial_partition_minus_value,polynomial_partition_plus_value,Nat.cast_sub hle]

theorem polynomial_partition_companion_diagonal_value (P : IV04.Paper.IntegerPartition) (i : Fin P.m) :
    fractionWordValue (polynomialPartitionCompanionDiagonal (pair P.inputCode i.val.bits)) = -P.s i/P.c i := by
  have hle : (P.weight i)^2 ≤ P.squaredScale := Nat.le_of_lt (P.squared_weight_lt_scale i)
  rw [P.companion_diagonal_scaled_fraction]
  simp [polynomialPartitionCompanionDiagonal,fractionWordValue,signedWordValue,firstBit,
    polynomial_partition_sine_numerator_value,polynomial_partition_minus_value,Nat.cast_sub hle]

theorem polynomial_partition_companion_beta_value (P : IV04.Paper.IntegerPartition) (i : Fin P.m) :
    fractionWordValue (polynomialPartitionCompanionBeta (pair P.inputCode i.val.bits)) = -1/P.c i := by
  have hle : (P.weight i)^2 ≤ P.squaredScale := Nat.le_of_lt (P.squared_weight_lt_scale i)
  rw [P.companion_beta_scaled_fraction]
  simp [polynomialPartitionCompanionBeta,fractionWordValue,signedWordValue,firstBit,
    polynomial_partition_plus_value,polynomial_partition_minus_value,Nat.cast_sub hle]

theorem polynomial_partition_threshold_fraction_value (P : IV04.Paper.IntegerPartition) :
    fractionWordValue (polynomialPartitionThresholdFraction P.inputCode) = P.threshold := by
  have hs : 0 < P.denominatorScale := by
    dsimp [IV04.Paper.IntegerPartition.denominatorScale]
    have := P.total_pos
    positivity
  have hq : 0 < P.squaredScale := by
    dsimp [IV04.Paper.IntegerPartition.squaredScale];positivity
  have hle : 1 ≤ 2*P.squaredScale := by omega
  rw [P.threshold_scaled_fraction]
  simp [polynomialPartitionThresholdFraction,fractionWordValue,signedWordValue,firstBit,
    polynomial_word_sub_value,wordValue,bitValue,polynomial_partition_squared_scale_value,
    Nat.cast_sub hle]
#print axioms polynomial_partition_sine_fraction_value
#print axioms polynomial_partition_cosine_fraction_value
#print axioms polynomial_partition_companion_diagonal_value
#print axioms polynomial_partition_companion_beta_value
#print axioms polynomial_partition_threshold_fraction_value
end IV04.Paper.Computational
