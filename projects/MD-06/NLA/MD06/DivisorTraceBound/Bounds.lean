module

public import NLA.MD06.DivisorTraceBound.Definitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06DivisorTrace
open scoped BigOperators

theorem actual_proper_divisor_le_half (t l : ℕ) (ht : 0 < t)
    (hl : l ∈ t.divisors.erase t) : l ≤ t / 2 := by
  have hmem := (Finset.mem_erase.mp hl).2
  have hne := (Finset.mem_erase.mp hl).1
  have hlpos := Nat.pos_of_mem_divisors hmem
  obtain ⟨k, hk⟩ := Nat.dvd_of_mem_divisors hmem
  have hk0 : k ≠ 0 := by intro h; simp [h] at hk; omega
  have hk1 : k ≠ 1 := by intro h; simp [h] at hk; omega
  have hk2 : 2 ≤ k := by omega
  have hmul : 2 * l ≤ t := by nlinarith
  omega

theorem actual_divisor_trace_denominator_positive (n t l : ℕ)
    (hn : 2 * t + 1 ≤ n) (hl : l ≤ t) :
    0 < 3 * (n : ℝ) - 2 * (l : ℝ) + 1 := by
  have hn' : 2 * (t : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hl' : (l : ℝ) ≤ (t : ℝ) := by exact_mod_cast hl
  have ht : 0 ≤ (t : ℝ) := by positivity
  linarith

theorem actual_divisor_trace_ratio_le_two (n t l : ℕ)
    (hn : 2 * t + 1 ≤ n) (hl : l ≤ t) :
    3 * (n : ℝ) / (3 * (n : ℝ) - 2 * (l : ℝ) + 1) ≤ 2 := by
  have hd := actual_divisor_trace_denominator_positive n t l hn hl
  have hn' : 2 * (t : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hl' : (l : ℝ) ≤ (t : ℝ) := by exact_mod_cast hl
  have ht : 0 ≤ (t : ℝ) := by positivity
  apply (div_le_iff₀ hd).2
  linarith

theorem actual_divisor_trace_leading_ratio (n t : ℕ)
    (hn : 2 * t + 1 ≤ n) :
    3 * (n : ℝ) / (3 * (n : ℝ) - 2 * (t : ℝ) + 1) ≤ 1 + (t : ℝ) / n := by
  have hd := actual_divisor_trace_denominator_positive n t t hn le_rfl
  have hn' : 2 * (t : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have ht : 0 ≤ (t : ℝ) := by positivity
  have hnp : 0 < (n : ℝ) := by linarith
  apply (div_le_iff₀ hd).2
  apply (mul_le_mul_iff_right₀ hnp).mp
  field_simp
  nlinarith

theorem actual_proper_divisor_trace_sum_bound (n t : ℕ) (ht : 0 < t)
    (hn : 2 * t + 1 ≤ n) :
    (∑ l ∈ t.divisors.erase t, 3 * (n : ℝ) * (2 : ℝ) ^ l /
      (3 * (n : ℝ) - 2 * (l : ℝ) + 1)) ≤ (n : ℝ) * (2 : ℝ) ^ (t / 2) := by
  have hb : ∀ l ∈ t.divisors.erase t,
      3 * (n : ℝ) * (2 : ℝ) ^ l / (3 * (n : ℝ) - 2 * (l : ℝ) + 1) ≤
        2 * (2 : ℝ) ^ (t / 2) := by
    intro l hl
    have hh := actual_proper_divisor_le_half t l ht hl
    have hlt : l ≤ t := Nat.le_of_dvd ht (Nat.dvd_of_mem_divisors (Finset.mem_erase.mp hl).2)
    have hr := actual_divisor_trace_ratio_le_two n t l hn hlt
    have hp : (2 : ℝ) ^ l ≤ (2 : ℝ) ^ (t / 2) := pow_le_pow_right₀ (by norm_num) hh
    calc
      _ = (3 * (n : ℝ) / (3 * (n : ℝ) - 2 * (l : ℝ) + 1)) * (2 : ℝ) ^ l := by ring
      _ ≤ 2 * (2 : ℝ) ^ l := mul_le_mul_of_nonneg_right hr (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  have hc : (t.divisors.erase t).card ≤ t :=
    (Finset.card_erase_le).trans (Nat.card_divisors_le_self t)
  have hcn : 2 * ((t.divisors.erase t).card : ℝ) ≤ (n : ℝ) := by
    have hc' : ((t.divisors.erase t).card : ℝ) ≤ (t : ℝ) := by exact_mod_cast hc
    have hn' : 2 * (t : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  calc
    _ ≤ ∑ _l ∈ t.divisors.erase t, 2 * (2 : ℝ) ^ (t / 2) := Finset.sum_le_sum hb
    _ = 2 * ((t.divisors.erase t).card : ℝ) * (2 : ℝ) ^ (t / 2) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcn (by positivity)

theorem actual_divisor_trace_sum_bound (n t : ℕ) (ht : 0 < t)
    (hn : 2 * t + 1 ≤ n) :
    DivisorTraceContribution n t ≤ (2 : ℝ) ^ t + (t : ℝ) * (2 : ℝ) ^ t / n +
      (n : ℝ) * (2 : ℝ) ^ (t / 2) := by
  have hm : t ∈ t.divisors := Nat.mem_divisors_self t (by omega)
  have hs := actual_proper_divisor_trace_sum_bound n t ht hn
  have hr := actual_divisor_trace_leading_ratio n t hn
  have htbound : 3 * (n : ℝ) * (2 : ℝ) ^ t / (3 * (n : ℝ) - 2 * (t : ℝ) + 1) ≤
      (2 : ℝ) ^ t + (t : ℝ) * (2 : ℝ) ^ t / n := by
    calc
      _ = (3 * (n : ℝ) / (3 * (n : ℝ) - 2 * (t : ℝ) + 1)) * (2 : ℝ) ^ t := by ring
      _ ≤ (1 + (t : ℝ) / n) * (2 : ℝ) ^ t := mul_le_mul_of_nonneg_right hr (by positivity)
      _ = _ := by ring
  unfold DivisorTraceContribution
  rw [← Finset.sum_erase_add _ _ hm]
  linarith

#print axioms actual_proper_divisor_le_half
#print axioms actual_divisor_trace_denominator_positive
#print axioms actual_divisor_trace_ratio_le_two
#print axioms actual_divisor_trace_leading_ratio
#print axioms actual_proper_divisor_trace_sum_bound
#print axioms actual_divisor_trace_sum_bound
end Reference.RootMD06DivisorTrace
