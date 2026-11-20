module

public import NLA.MD06.SimplicityExponentialLimit.Definitions
public import NLA.MD06.SimplicityBonferroni.Bonferroni
public import NLA.MD06.SimplicityBonferroni.Simplicity

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06SimplicityExponential
open Reference.MD06CubicConfiguration Reference.MD06Simplicity
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_alternating_binomial_zero (q : ℕ) :
    (∑ i ∈ Finset.range (q+1),(-1 : ℝ)^i*((0 : ℕ).choose i : ℝ))=1 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ,ih]
    simp [Nat.choose_eq_zero_of_lt (by omega : 0 < q+1)]

theorem actual_bonferroni_even_upper (m j : ℕ) :
    (if m=0 then (1 : ℝ) else 0) ≤
      ∑ i ∈ Finset.range (2*j+1),(-1 : ℝ)^i*(m.choose i : ℝ) := by
  cases m with
  | zero => rw [actual_alternating_binomial_zero (2*j)];simp
  | succ m =>
    rw [actual_alternating_binomial_partial_sum m (2*j)]
    simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false]
    simp [pow_mul]

theorem actual_bonferroni_odd_lower (m j : ℕ) :
    (∑ i ∈ Finset.range (2*j+1+1),(-1 : ℝ)^i*(m.choose i : ℝ)) ≤
      if m=0 then (1 : ℝ) else 0 := by
  cases m with
  | zero => rw [actual_alternating_binomial_zero (2*j+1)];simp
  | succ m =>
    rw [actual_alternating_binomial_partial_sum m (2*j+1)]
    simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false]
    simp [pow_add,pow_mul]

theorem actual_simple_indicator_even_upper {n : ℕ} (p : Pairing n) (j : ℕ) :
    (if IsSimplePairing p then (1 : ℝ) else 0) ≤
      ∑ i ∈ Finset.range (2*j+1),(-1 : ℝ)^i*((BadCount p).choose i : ℝ) := by
  simpa only [actual_simple_pairing_iff_bad_count_zero] using
    actual_bonferroni_even_upper (BadCount p) j

theorem actual_simple_indicator_odd_lower {n : ℕ} (p : Pairing n) (j : ℕ) :
    (∑ i ∈ Finset.range (2*j+1+1),(-1 : ℝ)^i*((BadCount p).choose i : ℝ)) ≤
      if IsSimplePairing p then (1 : ℝ) else 0 := by
  simpa only [actual_simple_pairing_iff_bad_count_zero] using
    actual_bonferroni_odd_lower (BadCount p) j

#print axioms actual_alternating_binomial_zero
#print axioms actual_bonferroni_even_upper
#print axioms actual_bonferroni_odd_lower
#print axioms actual_simple_indicator_even_upper
#print axioms actual_simple_indicator_odd_lower
end Reference.MD06SimplicityExponential
