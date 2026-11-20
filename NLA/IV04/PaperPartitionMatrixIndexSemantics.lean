module

public import NLA.IV04.PaperPartitionMatrixPoly
public import NLA.IV04.PaperPartitionFractionSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

theorem partition_and_flags (p q : Prop) [Decidable p] [Decidable q] :
    andBit [decide p] [decide q] = [decide (p ∧ q)] := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq,andBit,caseBit₀]

theorem partition_word_equal_value (left right : List Bool) :
    polynomialPartitionWordEqual (pair left right) = [decide (wordValue left = wordValue right)] := by
  simp only [polynomialPartitionWordEqual,pairFst_pair,pairSnd_pair,polynomial_word_le_value]
  rw [partition_and_flags]
  by_cases h : wordValue left = wordValue right
  · simp [h]
  · have hn : ¬(wordValue left ≤ wordValue right ∧ wordValue right ≤ wordValue left) :=
      fun hc => h (Nat.le_antisymm hc.1 hc.2)
    simp [h,hn]

theorem partition_word_mod_four (bits : List Bool) :
    wordValue bits % 4 = bitValue (firstBit bits) + 2*bitValue (firstBit bits.tail) := by
  cases bits with
  | nil => rfl
  | cons b bits =>
    cases bits with
    | nil => cases b <;> rfl
    | cons c bits =>
      have hb := bit_value_le_one b
      have hc := bit_value_le_one c
      simp only [wordValue,firstBit,List.headD_cons,List.tail_cons]
      omega

theorem partition_word_tail_tail (bits : List Bool) :
    wordValue bits.tail.tail = wordValue bits / 4 := by
  cases bits with
  | nil => rfl
  | cons b bits =>
    cases bits with
    | nil => cases b <;> rfl
    | cons c bits =>
      have hb := bit_value_le_one b
      have hc := bit_value_le_one c
      simp only [wordValue,List.tail_cons]
      omega

theorem partition_mod_zero_value (bits : List Bool) :
    polynomialPartitionModZero bits = [decide (wordValue bits % 4 = 0)] := by
  simp only [polynomialPartitionModZero,head_flag]
  rw [partition_word_mod_four]
  generalize firstBit bits = b
  generalize firstBit bits.tail = c
  cases b <;> cases c <;> simp [bitValue,notBit,andBit,caseBit₀]

theorem partition_mod_one_value (bits : List Bool) :
    polynomialPartitionModOne bits = [decide (wordValue bits % 4 = 1)] := by
  simp only [polynomialPartitionModOne,head_flag]
  rw [partition_word_mod_four]
  generalize firstBit bits = b
  generalize firstBit bits.tail = c
  cases b <;> cases c <;> simp [bitValue,notBit,andBit,caseBit₀]

theorem partition_mod_two_value (bits : List Bool) :
    polynomialPartitionModTwo bits = [decide (wordValue bits % 4 = 2)] := by
  simp only [polynomialPartitionModTwo,head_flag]
  rw [partition_word_mod_four]
  generalize firstBit bits = b
  generalize firstBit bits.tail = c
  cases b <;> cases c <;> simp [bitValue,notBit,andBit,caseBit₀]

theorem partition_quarter_word (bits : List Bool) :
    polynomialPartitionQuarter bits = (wordValue bits / 4).bits := by
  simp only [polynomialPartitionQuarter,canonical_word_eq_bits,partition_word_tail_tail]

theorem partition_reverse_index_word (left right : List Bool) :
    polynomialPartitionReverseIndex (pair left right) = (wordValue left - 1 - wordValue right).bits := by
  simp [polynomialPartitionReverseIndex,pairFst_pair,pairSnd_pair,canonical_word_eq_bits,
    polynomial_word_sub_value,wordValue,bitValue]

theorem partition_layer_count_word (P : IV04.Paper.IntegerPartition) :
    polynomialPartitionLayerCount P.inputCode = P.layerCount.bits := by
  have h := polynomial_partition_layer_count_value P
  simp only [polynomialPartitionLayerCount,canonical_word_value] at h
  simp only [polynomialPartitionLayerCount,canonical_word_eq_bits]
  exact congrArg Nat.bits h

#print axioms partition_word_equal_value
#print axioms partition_word_mod_four
#print axioms partition_word_tail_tail
#print axioms partition_mod_zero_value
#print axioms partition_mod_one_value
#print axioms partition_mod_two_value
#print axioms partition_quarter_word
#print axioms partition_reverse_index_word
#print axioms partition_layer_count_word
end IV04.Paper.Computational
