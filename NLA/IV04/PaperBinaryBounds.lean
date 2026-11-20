module

public import NLA.IV04.PaperBinaryDefinitions
public import NLA.IV04.PaperPartitionRotations
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper

theorem sum_lt_two_pow_sum_size {ι : Type*} (S : Finset ι) (w : ι → ℕ) :
    (∑ i ∈ S, w i) < 2^(∑ i ∈ S, (w i).size) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pow_add]
    have ha' : w a+1 ≤ 2^(w a).size := Nat.lt_size_self (w a)
    have hS : (∑ i ∈ S, w i)+1 ≤ 2^(∑ i ∈ S, (w i).size) := ih
    have hprod := Nat.mul_le_mul ha' hS
    have hsum : w a+(∑ i ∈ S, w i)+1 ≤
        (w a+1)*((∑ i ∈ S, w i)+1) := by
      nlinarith [Nat.zero_le (w a*(∑ i ∈ S, w i))]
    exact lt_of_lt_of_le (Nat.lt_of_succ_le hsum) hprod

namespace IntegerPartition

theorem total_lt_binary_bound (P : IntegerPartition) :
    P.total < 2^P.inputBits := by
  simpa [total,inputBits] using sum_lt_two_pow_sum_size Finset.univ P.weight

theorem dimension_le_input_bits (P : IntegerPartition) : P.m ≤ P.inputBits := by
  have h : (∑ _i : Fin P.m, 1) ≤ ∑ i : Fin P.m, (P.weight i).size :=
    Finset.sum_le_sum (fun i _ => Nat.size_pos.mpr (P.positive i))
  simpa [inputBits] using h

theorem squared_scale_identity (P : IntegerPartition) :
    P.squaredScale = 100*P.total^4 := by
  dsimp [squaredScale,denominatorScale]
  ring

theorem squared_weight_lt_scale (P : IntegerPartition) (i : Fin P.m) :
    (P.weight i)^2 < P.squaredScale := by
  have hw := weight_le_total P i
  have hp := total_pos P
  have hs : (P.weight i)^2 ≤ P.total^2 := Nat.pow_le_pow_left hw 2
  have hW : 1 ≤ P.total^2 := by
    have : 0 < P.total^2 := by positivity
    omega
  have hmul : P.total^2 ≤ P.total^4 := by
    calc P.total^2 = P.total^2*1 := by simp
         _ ≤ P.total^2*P.total^2 := Nat.mul_le_mul_left _ hW
         _ = P.total^4 := by ring
  rw [squared_scale_identity]
  nlinarith

theorem entry_magnitude_lt_binary_bound (P : IntegerPartition) :
    P.entryMagnitudeBound < 2^P.entryBitBound := by
  have hW := total_lt_binary_bound P
  have hpow : P.total^4 < (2^P.inputBits)^4 := Nat.pow_lt_pow_left hW (by decide)
  have hp : 0 < (2^P.inputBits)^4 := by positivity
  have h : 200*P.total^4 < 256*(2^P.inputBits)^4 := by nlinarith
  have he : (2^P.inputBits)^4 = 2^(4*P.inputBits) := by
    rw [← pow_mul,Nat.mul_comm]
  rw [he] at h
  simpa [entryMagnitudeBound,entryBitBound,pow_add,Nat.mul_comm] using h

theorem magnitude_size_bound (P : IntegerPartition) (n : ℕ)
    (hn : n ≤ P.entryMagnitudeBound) : n.size ≤ P.entryBitBound :=
  Nat.size_le.mpr (lt_of_le_of_lt hn (entry_magnitude_lt_binary_bound P))

theorem rotation_denominator_bound (P : IntegerPartition) (i : Fin P.m) :
    P.squaredScale+(P.weight i)^2 ≤ P.entryMagnitudeBound := by
  have hw := squared_weight_lt_scale P i
  rw [squared_scale_identity] at hw ⊢
  dsimp [entryMagnitudeBound]
  omega

theorem positive_companion_denominator (P : IntegerPartition) (i : Fin P.m) :
    0 < P.squaredScale-(P.weight i)^2 :=
  Nat.sub_pos_of_lt (squared_weight_lt_scale P i)

theorem companion_denominator_bound (P : IntegerPartition) (i : Fin P.m) :
    P.squaredScale-(P.weight i)^2 ≤ P.entryMagnitudeBound := by
  have h := Nat.sub_le P.squaredScale ((P.weight i)^2)
  rw [squared_scale_identity] at h
  rw [squared_scale_identity]
  dsimp [entryMagnitudeBound]
  omega

theorem sine_numerator_bound (P : IntegerPartition) (i : Fin P.m) :
    2*P.weight i*P.denominatorScale ≤ P.entryMagnitudeBound := by
  have hw := weight_le_total P i
  have hW : 1 ≤ P.total := total_pos P
  have h3 : P.total^3 ≤ P.total^4 := by
    calc P.total^3 = P.total^3*1 := by simp
         _ ≤ P.total^3*P.total := Nat.mul_le_mul_left _ hW
         _ = P.total^4 := by ring
  have h : 2*P.weight i*P.denominatorScale ≤ 20*P.total^3 := by
    dsimp [denominatorScale]
    nlinarith [Nat.mul_le_mul_right (10*P.total^2) hw]
  dsimp [entryMagnitudeBound]
  nlinarith

theorem threshold_denominator_bound (P : IntegerPartition) :
    2*P.squaredScale = P.entryMagnitudeBound := by
  rw [squared_scale_identity]
  dsimp [entryMagnitudeBound]
  ring

theorem rotation_denominator_bits (P : IntegerPartition) (i : Fin P.m) :
    (P.squaredScale+(P.weight i)^2).size ≤ P.entryBitBound :=
  magnitude_size_bound P _ (rotation_denominator_bound P i)

theorem companion_denominator_bits (P : IntegerPartition) (i : Fin P.m) :
    (P.squaredScale-(P.weight i)^2).size ≤ P.entryBitBound :=
  magnitude_size_bound P _ (companion_denominator_bound P i)

theorem sine_numerator_bits (P : IntegerPartition) (i : Fin P.m) :
    (2*P.weight i*P.denominatorScale).size ≤ P.entryBitBound :=
  magnitude_size_bound P _ (sine_numerator_bound P i)

theorem threshold_denominator_bits (P : IntegerPartition) :
    (2*P.squaredScale).size ≤ P.entryBitBound :=
  magnitude_size_bound P _ (le_of_eq (threshold_denominator_bound P))

end IntegerPartition
end IV04.Paper
