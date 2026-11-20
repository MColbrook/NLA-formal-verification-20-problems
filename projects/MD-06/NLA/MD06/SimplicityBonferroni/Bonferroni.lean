module

public import NLA.MD06.SimplicityBonferroni.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Simplicity
open Reference.MD06CubicConfiguration
open scoped BigOperators

theorem actual_alternating_binomial_partial_sum (t q : ℕ) :
    (∑ i ∈ Finset.range (q+1), (-1 : ℝ)^i * ((t+1).choose i : ℝ)) =
      (-1 : ℝ)^q * (t.choose q : ℝ) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ,ih,Nat.choose_succ_succ,Nat.cast_add,pow_succ]
    ring

theorem actual_bonferroni_seven_pointwise (m : ℕ) :
    (∑ i ∈ Finset.range 8, (-1 : ℝ)^i * (m.choose i : ℝ)) ≤
      if m = 0 then (1 : ℝ) else 0 := by
  cases m with
  | zero => norm_num [Finset.sum_range_succ]
  | succ t =>
    have h := actual_alternating_binomial_partial_sum t 7
    norm_num at h ⊢
    rw [h]
    exact neg_nonpos.mpr (Nat.cast_nonneg _)

theorem actual_pairing_bad_bonferroni_seven {n : ℕ} (p : Pairing n) :
    (∑ i ∈ Finset.range 8, (-1 : ℝ)^i * ((BadCount p).choose i : ℝ)) ≤
      if BadCount p = 0 then (1 : ℝ) else 0 :=
  actual_bonferroni_seven_pointwise (BadCount p)

theorem actual_mean_two_bonferroni_seven_value :
    (∑ i ∈ Finset.range 8, (-1 : ℝ)^i * ((2 : ℝ)^i / (i.factorial : ℝ))) =
      41/315 := by norm_num [Finset.sum_range_succ]

theorem actual_mean_two_bonferroni_seven_positive :
    0 < (∑ i ∈ Finset.range 8, (-1 : ℝ)^i * ((2 : ℝ)^i / (i.factorial : ℝ))) := by
  rw [actual_mean_two_bonferroni_seven_value]
  norm_num

#print axioms actual_alternating_binomial_partial_sum
#print axioms actual_bonferroni_seven_pointwise
#print axioms actual_pairing_bad_bonferroni_seven
#print axioms actual_mean_two_bonferroni_seven_value
#print axioms actual_mean_two_bonferroni_seven_positive
end Reference.MD06Simplicity