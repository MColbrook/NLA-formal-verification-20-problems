module

public import NLA.IV04.PaperCommonDenominatorDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational

theorem common_denominator_positive {k : ℕ} (q : Fin k → ℚ) :
    0 < rationalCommonDenominator q := by
  apply Finset.prod_pos
  intro i _
  exact (q i).pos

theorem common_denominator_divisible {k : ℕ} (q : Fin k → ℚ) (i : Fin k) :
    (q i).den ∣ rationalCommonDenominator q := by
  exact Finset.dvd_prod_of_mem (fun j => (q j).den) (Finset.mem_univ i)

theorem coefficient_size_le_payload {k : ℕ} (q : Fin k → ℚ) (i : Fin k) :
    (q i).num.natAbs.size ≤ rationalPayloadBits q ∧
      (q i).den.size ≤ rationalPayloadBits q := by
  have h : (q i).num.natAbs.size+(q i).den.size ≤ rationalPayloadBits q := by
    simpa only [rationalPayloadBits] using
      Finset.single_le_sum (f := fun j : Fin k => (q j).num.natAbs.size+(q j).den.size)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

theorem coefficient_count_le_payload {k : ℕ} (q : Fin k → ℚ) :
    k ≤ rationalPayloadBits q := by
  have h : (∑ _i : Fin k, 1) ≤ ∑ i : Fin k, ((q i).num.natAbs.size+(q i).den.size) := by
    apply Finset.sum_le_sum
    intro i _
    have hp : 0 < (q i).den.size := Nat.size_pos.mpr (q i).pos
    omega
  simpa [rationalPayloadBits] using h

theorem common_denominator_binary_bound {k : ℕ} (q : Fin k → ℚ) :
    rationalCommonDenominator q ≤ 2^rationalPayloadBits q := by
  have hsum : (∑ i : Fin k, (q i).den.size) ≤ rationalPayloadBits q := by
    apply Finset.sum_le_sum
    intro i _
    omega
  calc
    rationalCommonDenominator q ≤ ∏ i : Fin k, 2^(q i).den.size := by
      apply Finset.prod_le_prod
      intro i _
      exact Nat.le_of_lt (Nat.lt_size_self (q i).den)
    _ = 2^(∑ i : Fin k, (q i).den.size) := by
      simpa using Finset.prod_pow_eq_pow_sum Finset.univ (fun i : Fin k => (q i).den.size) 2
    _ ≤ 2^rationalPayloadBits q := Nat.pow_le_pow_right (by decide) hsum

theorem common_numerator_fraction {k : ℕ} (q : Fin k → ℚ) (i : Fin k) :
    (rationalCommonNumerator q i : ℚ)/(rationalCommonDenominator q : ℚ)=q i := by
  have hd : (rationalCommonDenominator q : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (common_denominator_positive q))
  have hi : ((q i).den : ℚ) ≠ 0 := by exact_mod_cast (q i).den_nz
  simp only [rationalCommonNumerator,Int.cast_mul,Int.cast_natCast]
  rw [Nat.cast_div (common_denominator_divisible q i) hi]
  conv_rhs => rw [← Rat.num_div_den (q i)]
  field_simp

theorem common_numerator_binary_bound {k : ℕ} (q : Fin k → ℚ) (i : Fin k) :
    (rationalCommonNumerator q i).natAbs ≤ 2^(2*rationalPayloadBits q) := by
  have hnum : (q i).num.natAbs ≤ 2^rationalPayloadBits q := by
    exact (Nat.le_of_lt (Nat.lt_size_self (q i).num.natAbs)).trans
      (Nat.pow_le_pow_right (by decide) (coefficient_size_le_payload q i).1)
  have hd : rationalCommonDenominator q/(q i).den ≤ 2^rationalPayloadBits q :=
    (Nat.div_le_self _ _).trans (common_denominator_binary_bound q)
  have h := Nat.mul_le_mul hnum hd
  simpa only [rationalCommonNumerator,Int.natAbs_mul,Int.natAbs_natCast,
    ← pow_add,show rationalPayloadBits q+rationalPayloadBits q=2*rationalPayloadBits q by omega] using h

#print axioms common_numerator_fraction
end IV04.Paper.Computational
