module

public import NLA.IV04.PaperBinaryFractions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.IntegerPartition

theorem fraction_bits (P : IntegerPartition) (a : ℤ) (b : ℕ) (hb : 0 < b)
    (ha : a.natAbs ≤ P.entryMagnitudeBound) (hbb : b ≤ P.entryMagnitudeBound) :
    (((a : ℚ)/(b : ℚ)).num.natAbs).size ≤ P.entryBitBound ∧
      (((a : ℚ)/(b : ℚ)).den).size ≤ P.entryBitBound := by
  have h := reduced_fraction_payload a b hb
  exact ⟨magnitude_size_bound P _ (h.1.trans ha),
    magnitude_size_bound P _ (h.2.trans hbb)⟩

theorem cosine_nat_fraction (P : IntegerPartition) (i : Fin P.m) :
    P.c i = ((P.squaredScale-(P.weight i)^2 : ℕ) : ℚ)/
      ((P.squaredScale+(P.weight i)^2 : ℕ) : ℚ) := by
  simpa only [Nat.cast_sub (le_of_lt (squared_weight_lt_scale P i)),
    Nat.cast_pow,Nat.cast_add] using cosine_scaled_fraction P i

theorem sine_nat_fraction (P : IntegerPartition) (i : Fin P.m) :
    P.s i = ((2*P.weight i*P.denominatorScale : ℕ) : ℚ)/
      ((P.squaredScale+(P.weight i)^2 : ℕ) : ℚ) := by
  simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,Nat.cast_add]
    using sine_scaled_fraction P i

theorem companion_diagonal_nat_fraction (P : IntegerPartition) (i : Fin P.m) :
    -P.s i/P.c i = -((2*P.weight i*P.denominatorScale : ℕ) : ℚ)/
      ((P.squaredScale-(P.weight i)^2 : ℕ) : ℚ) := by
  simpa only [Nat.cast_sub (le_of_lt (squared_weight_lt_scale P i)),
    Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow] using companion_diagonal_scaled_fraction P i

theorem companion_beta_nat_fraction (P : IntegerPartition) (i : Fin P.m) :
    -1/P.c i = -((P.squaredScale+(P.weight i)^2 : ℕ) : ℚ)/
      ((P.squaredScale-(P.weight i)^2 : ℕ) : ℚ) := by
  simpa only [Nat.cast_sub (le_of_lt (squared_weight_lt_scale P i)),
    Nat.cast_pow,Nat.cast_add] using companion_beta_scaled_fraction P i

theorem threshold_nat_fraction (P : IntegerPartition) :
    P.threshold = ((2*P.squaredScale-1 : ℕ) : ℚ)/((2*P.squaredScale : ℕ) : ℚ) := by
  have hp : 1 ≤ 2*P.squaredScale := by
    have h := squared_weight_lt_scale P P.lastIndex
    omega
  simpa only [Nat.cast_sub hp,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    using threshold_scaled_fraction P

theorem cosine_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (P.c i).num.natAbs.size ≤ P.entryBitBound ∧ (P.c i).den.size ≤ P.entryBitBound := by
  rw [cosine_nat_fraction]
  have hp : 0 < P.squaredScale+(P.weight i)^2 := by
    have h := squared_weight_lt_scale P i
    omega
  simpa only [Int.natAbs_natCast,Int.cast_natCast] using
    fraction_bits P ((P.squaredScale-(P.weight i)^2 : ℕ) : ℤ)
      (P.squaredScale+(P.weight i)^2) hp
      (by simpa using companion_denominator_bound P i) (rotation_denominator_bound P i)

theorem sine_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (P.s i).num.natAbs.size ≤ P.entryBitBound ∧ (P.s i).den.size ≤ P.entryBitBound := by
  rw [sine_nat_fraction]
  have hp : 0 < P.squaredScale+(P.weight i)^2 := by
    have h := squared_weight_lt_scale P i
    omega
  simpa only [Int.natAbs_natCast,Int.cast_natCast] using
    fraction_bits P ((2*P.weight i*P.denominatorScale : ℕ) : ℤ)
      (P.squaredScale+(P.weight i)^2) hp
      (by simpa only [Int.natAbs_natCast] using sine_numerator_bound P i)
      (rotation_denominator_bound P i)

theorem companion_diagonal_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (-P.s i/P.c i).num.natAbs.size ≤ P.entryBitBound ∧
      (-P.s i/P.c i).den.size ≤ P.entryBitBound := by
  rw [companion_diagonal_nat_fraction]
  simpa only [Int.natAbs_neg,Int.natAbs_natCast,Int.cast_neg,Int.cast_natCast] using
    fraction_bits P (-((2*P.weight i*P.denominatorScale : ℕ) : ℤ))
      (P.squaredScale-(P.weight i)^2) (positive_companion_denominator P i)
      (by simpa only [Int.natAbs_neg,Int.natAbs_natCast] using sine_numerator_bound P i)
      (companion_denominator_bound P i)

theorem companion_beta_payload_bits (P : IntegerPartition) (i : Fin P.m) :
    (-1/P.c i).num.natAbs.size ≤ P.entryBitBound ∧
      (-1/P.c i).den.size ≤ P.entryBitBound := by
  rw [companion_beta_nat_fraction]
  simpa only [Int.natAbs_neg,Int.natAbs_natCast,Int.cast_neg,Int.cast_natCast] using
    fraction_bits P (-((P.squaredScale+(P.weight i)^2 : ℕ) : ℤ))
      (P.squaredScale-(P.weight i)^2) (positive_companion_denominator P i)
      (by simpa only [Int.natAbs_neg,Int.natAbs_natCast] using rotation_denominator_bound P i)
      (companion_denominator_bound P i)

theorem threshold_payload_bits (P : IntegerPartition) :
    P.threshold.num.natAbs.size ≤ P.entryBitBound ∧
      P.threshold.den.size ≤ P.entryBitBound := by
  rw [threshold_nat_fraction]
  have hp : 0 < 2*P.squaredScale := by
    have h := squared_weight_lt_scale P P.lastIndex
    omega
  simpa only [Int.natAbs_natCast,Int.cast_natCast] using
    fraction_bits P ((2*P.squaredScale-1 : ℕ) : ℤ) (2*P.squaredScale) hp
      (by simpa only [Int.natAbs_natCast] using
        (Nat.sub_le (2*P.squaredScale) 1).trans (le_of_eq (threshold_denominator_bound P)))
      (le_of_eq (threshold_denominator_bound P))

end IV04.Paper.IntegerPartition
