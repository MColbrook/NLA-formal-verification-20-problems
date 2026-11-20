module

public import NLA.MD06.DivisorTraceBound.Bounds

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06DivisorTrace

theorem actual_dyadic_walk_length_admissible (k : ℕ) (hk : 6 ≤ k) :
    2 * (4 * k) + 1 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    omega

theorem actual_quartic_walk_error_coefficient (x : ℝ) (hx : 0 ≤ x) :
    27 * (4 * x) ^ 2 * (4 * x + 1) ^ 2 + 4 * x ≤ 10804 * (x + 1) ^ 4 := by
  have h3 : 0 ≤ x ^ 3 := pow_nonneg hx _
  have h4 : 0 ≤ x ^ 4 := pow_nonneg hx _
  nlinarith [sq_nonneg x]

theorem actual_dyadic_divisor_trace_sum_bound (n k : ℕ) (hk : 6 ≤ k)
    (hn : 2 ^ k ≤ n) :
    DivisorTraceContribution n (4 * k) ≤ (2 : ℝ) ^ (4 * k) +
      (4 * (k : ℝ)) * (2 : ℝ) ^ (4 * k) / n +
      (n : ℝ) * (2 : ℝ) ^ (2 * k) := by
  have h := actual_divisor_trace_sum_bound n (4 * k) (by omega)
    ((actual_dyadic_walk_length_admissible k hk).trans hn)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, show 4 * k / 2 = 2 * k by omega] using h

theorem actual_quartic_trace_error_combination (n k : ℕ) :
    (27 * (4 * (k : ℝ)) ^ 2 * (4 * (k : ℝ) + 1) ^ 2 + 4 * (k : ℝ)) *
        (2 : ℝ) ^ (4 * k) / n ≤
      10804 * ((k : ℝ) + 1) ^ 4 * (2 : ℝ) ^ (4 * k) / n := by
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (actual_quartic_walk_error_coefficient k (by positivity))
      (by positivity)) (by positivity)

#print axioms actual_dyadic_walk_length_admissible
#print axioms actual_quartic_walk_error_coefficient
#print axioms actual_dyadic_divisor_trace_sum_bound
#print axioms actual_quartic_trace_error_combination
end Reference.RootMD06DivisorTrace
