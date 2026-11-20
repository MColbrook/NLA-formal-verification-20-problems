module

public import NLA.IV04.PaperPartitionMatrixIndexSemantics
public import NLA.IV04.PaperCubeDefinitions
public import NLA.IV04.PaperRationalListParserDefinitions
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem partition_case_decide (p : Prop) [Decidable p] (yes no : List Bool) :
    caseBit₀ [decide p] yes no = if p then yes else no := by
  by_cases hp : p <;> simp [hp,caseBit₀]

theorem partition_bits_value (n : ℕ) : wordValue n.bits = n := by
  rw [word_value_foldr];exact IV04.Paper.bits_foldr n

theorem partition_fraction_zero : fractionWordValue (pair [false] [true]) = (0 : ℚ) := by
  norm_num [fractionWordValue,signedWordValue,firstBit,wordValue,bitValue]
theorem partition_fraction_one : fractionWordValue (pair [false,true] [true]) = (1 : ℚ) := by
  norm_num [fractionWordValue,signedWordValue,firstBit,wordValue,bitValue]
theorem partition_fraction_minus_one : fractionWordValue (pair [true,true] [true]) = (-1 : ℚ) := by
  norm_num [fractionWordValue,signedWordValue,firstBit,wordValue,bitValue]

theorem polynomial_partition_negative_cosine_value (P : IV04.Paper.IntegerPartition) (i : Fin P.m) :
    fractionWordValue (polynomialPartitionNegativeCosine (pair P.inputCode i.val.bits)) = -P.c i := by
  have hle : (P.weight i)^2 ≤ P.squaredScale := Nat.le_of_lt (P.squared_weight_lt_scale i)
  rw [P.cosine_scaled_fraction]
  simp [polynomialPartitionNegativeCosine,fractionWordValue,signedWordValue,firstBit,
    polynomial_partition_minus_value,polynomial_partition_plus_value,Nat.cast_sub hle]
  ring

theorem polynomial_partition_lower_fraction_value (P : IV04.Paper.IntegerPartition)
    (i j : Fin P.layerCount) :
    fractionWordValue (polynomialPartitionLowerFraction
      (pair P.inputCode (pair i.val.bits j.val.bits))) = P.rationalLower i j := by
  have hk : i.val / 4 < P.m := by
    have := i.isLt
    dsimp [IV04.Paper.IntegerPartition.layerCount] at this
    omega
  let k : Fin P.m := ⟨i.val/4,hk⟩
  have hq : polynomialPartitionQuarter i.val.bits = k.val.bits := by
    rw [partition_quarter_word,partition_bits_value]
  have hs := polynomial_partition_sine_fraction_value P k
  have hd := polynomial_partition_companion_diagonal_value P k
  have hc := polynomial_partition_negative_cosine_value P k
  have hb := polynomial_partition_companion_beta_value P k
  have he : i.val = j.val ↔ i = j := Fin.ext_iff.symm
  simp only [polynomialPartitionLowerFraction,pairFst_pair,pairSnd_pair,
    partition_word_equal_value,partition_mod_zero_value,partition_mod_one_value,
    polynomial_word_add_value,partition_bits_value,wordValue,bitValue,if_true,
    Nat.mul_zero,Nat.add_zero,partition_case_decide,he,hq]
  unfold IV04.Paper.IntegerPartition.rationalLower
  by_cases hij : i = j
  · simp only [if_pos hij]
    by_cases h0 : i.val % 4 = 0
    · simp only [IV04.Paper.IntegerPartition.layerDiagonal,if_pos h0,hs,
        IV04.Paper.IntegerPartition.sAt,dif_pos hk]
      rfl
    · by_cases h1 : i.val % 4 = 1
      · simp only [IV04.Paper.IntegerPartition.layerDiagonal,if_neg h0,if_pos h1,hd,
          IV04.Paper.IntegerPartition.sAt,IV04.Paper.IntegerPartition.cAt,dif_pos hk]
        rfl
      · simp only [IV04.Paper.IntegerPartition.layerDiagonal,if_neg h0,if_neg h1,
          partition_fraction_zero]
  · simp only [if_neg hij]
    by_cases hu : j.val = i.val+1
    · simp only [if_pos hu,partition_fraction_one]
    · simp only [if_neg hu]
      by_cases hl : i.val = j.val+1
      · simp only [if_pos hl]
        by_cases h0 : i.val % 4 = 0
        · simp only [if_pos h0,hc,IV04.Paper.IntegerPartition.cAt,dif_pos hk]
          rfl
        · by_cases h1 : i.val % 4 = 1
          · simp only [if_neg h0,if_pos h1,hb,IV04.Paper.IntegerPartition.cAt,dif_pos hk]
            rfl
          · simp only [if_neg h0,if_neg h1,partition_fraction_minus_one]
      · simp only [if_neg hl,partition_fraction_zero]

theorem polynomial_partition_upper_fraction_value (P : IV04.Paper.IntegerPartition)
    (i j : Fin P.layerCount) :
    fractionWordValue (polynomialPartitionUpperFraction
      (pair P.inputCode (pair i.val.bits j.val.bits))) = P.rationalUpper i j := by
  have hl := polynomial_partition_lower_fraction_value P i j
  simp only [polynomialPartitionUpperFraction,pairFst_pair,pairSnd_pair,
    partition_word_equal_value,partition_mod_two_value,polynomial_word_add_value,
    partition_bits_value,wordValue,bitValue,if_true,Nat.mul_zero,Nat.add_zero,
    partition_and_flags,partition_case_decide]
  by_cases h : i.val = j.val+1 ∧ i.val%4=2
  · simp only [if_pos h,partition_fraction_one,IV04.Paper.IntegerPartition.rationalUpper,if_pos h]
  · simp only [if_neg h,hl,IV04.Paper.IntegerPartition.rationalUpper,if_neg h]

theorem polynomial_partition_endpoint_fields_read (P : IV04.Paper.IntegerPartition)
    (i j : Fin P.layerCount) (tail : List Bool) :
    readRationals 2 (polynomialPartitionEndpointFields
      (pair P.inputCode (pair i.val.bits j.val.bits)) ++ tail) =
      some ([P.rationalLower i j,P.rationalUpper i j],tail) := by
  simp only [polynomialPartitionEndpointFields,List.append_assoc,readRationals,
    polynomial_fraction_output_read,bind,Option.bind_some,
    polynomial_partition_lower_fraction_value,polynomial_partition_upper_fraction_value]
  rfl

#print axioms polynomial_partition_negative_cosine_value
#print axioms polynomial_partition_lower_fraction_value
#print axioms polynomial_partition_upper_fraction_value
#print axioms polynomial_partition_endpoint_fields_read
end IV04.Paper.Computational
