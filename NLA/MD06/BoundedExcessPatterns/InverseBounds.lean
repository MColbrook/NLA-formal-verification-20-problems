module

public import NLA.MD06.BoundedExcessPatterns.BoundDefinitions
public import NLA.MD06.BoundedExcessPatterns.EventBounds
public import NLA.MD06.CycleMoments.PatternLimits

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06BoundedExcess
open Reference.MD06CycleMoments Reference.MD06WeightedOverlap Reference.MD06FiniteProbability
open Reference.MD06PairingCounts
open Filter Topology
open scoped BigOperators

theorem actual_constraint_inverse_size_bound (v e : ℕ) (hve : v<e) :
    ∀ᶠk : ℕ in atTop,
      ConstraintMean (Size k) v e≤
        (((2^(9*v^2) : ℕ) : ℝ)*(2/(3 : ℝ)^e))/(Size k : ℝ) := by
  have hd := actual_size_tendsto_atTop.eventually (actual_scaled_pattern_denominator_eventual_bound e)
  filter_upwards [hd] with k hk
  have hn : 1≤(Size k : ℝ) := by exact_mod_cast (show 1≤Size k from by unfold Size;omega)
  have hnp : 0<(Size k : ℝ) := lt_of_lt_of_le zero_lt_one hn
  have hp : (Size k : ℝ)^(v+1)≤(Size k : ℝ)^e :=
    pow_le_pow_right₀ hn (by omega)
  apply (le_div_iff₀ hnp).mpr
  rw [mul_comm]
  calc
    (Size k : ℝ)*ConstraintMean (Size k) v e≤
        (Size k : ℝ)*(((Size k : ℝ)^v*(2^(9*v^2) : ℕ))/(PairingDenominator (Size k) e : ℝ)) :=
      mul_le_mul_of_nonneg_left (actual_constraint_mean_finite_bound k v e) hnp.le
    _ = ((Size k : ℝ)^(v+1)/(PairingDenominator (Size k) e : ℝ))*((2^(9*v^2) : ℕ) : ℝ) := by
      rw [pow_succ]
      ring
    _ ≤ ((Size k : ℝ)^e/(PairingDenominator (Size k) e : ℝ))*((2^(9*v^2) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    _ ≤ (2/(3 : ℝ)^e)*((2^(9*v^2) : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _)
    _ = _ := mul_comm _ _

theorem actual_total_inverse_size_bound (K : ℕ) :
    ∀ᶠk : ℕ in atTop,
      TotalConstraintMean (Size k) K≤BoundConstant K/(Size k : ℝ) := by
  have hs : ∀ᶠk : ℕ in atTop,∀s : ExcessShape K,
      ConstraintMean (Size k) s.val.1.val s.val.2.val≤
        (((2^(9*s.val.1.val^2) : ℕ) : ℝ)*(2/(3 : ℝ)^s.val.2.val))/(Size k : ℝ) :=
    eventually_all.mpr (fun s =>
      actual_constraint_inverse_size_bound s.val.1.val s.val.2.val s.property)
  filter_upwards [hs] with k hk
  rw [actual_total_constraint_mean_shape_sum,BoundConstant,Finset.sum_div]
  apply Finset.sum_le_sum
  intro s _
  exact hk s

theorem actual_bounded_excess_inverse_size_bound (K : ℕ) :
    ∀ᶠk : ℕ in atTop,
      ExcessProbability k K≤BoundConstant K/(Size k : ℝ) := by
  filter_upwards [actual_total_inverse_size_bound K] with k hk
  exact (actual_excess_probability_le_mean k K).trans hk

theorem actual_bound_constant_nonnegative (K : ℕ) : 0≤BoundConstant K := by
  unfold BoundConstant
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (by positivity))

#print axioms actual_constraint_inverse_size_bound
#print axioms actual_total_inverse_size_bound
#print axioms actual_bounded_excess_inverse_size_bound
#print axioms actual_bound_constant_nonnegative
end Reference.MD06BoundedExcess
