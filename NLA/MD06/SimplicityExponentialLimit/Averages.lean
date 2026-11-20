module

public import NLA.MD06.SimplicityExponentialLimit.Pointwise
public import NLA.MD06.SimplicityBonferroni.Average
public import NLA.MD06.BadJointMoments.JointCounts
public import NLA.MD06.DisjointTypedEnumeration.AllBadMoments

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06SimplicityExponential
open Reference.MD06CubicConfiguration Reference.MD06Simplicity Reference.MD06FiniteProbability
open Reference.MD06BadJointMoments Reference.MD06DisjointTypedEnumeration
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_partial_moment_average (k t : ℕ) :
    PartialMoment k t =
      (∑ p : Pairing (Size k),∑ i ∈ Finset.range (t+1),
        (-1 : ℝ)^i*((BadCount p).choose i : ℝ))/
          (Fintype.card (Pairing (Size k)) : ℝ) := by
  unfold PartialMoment
  simp_rw [←actual_mean_bad_choose_descending]
  change (∑ i ∈ Finset.range (t+1),(-1 : ℝ)^i*
    ((∑ p : Pairing (Size k),((BadCount p).choose i : ℝ))/
      (Fintype.card (Pairing (Size k)) : ℝ))) = _
  simp_rw [←mul_div_assoc,Finset.mul_sum]
  rw [←Finset.sum_div,Finset.sum_comm]

theorem actual_simple_probability_indicator_average (k : ℕ) :
    SimpleProbability k =
      (∑ p : Pairing (Size k),if IsSimplePairing p then (1 : ℝ) else 0)/
        (Fintype.card (Pairing (Size k)) : ℝ) := by
  rw [actual_simple_indicator_sum]
  unfold SimpleProbability
  rw [actual_pairing_probability_uniform_real]
  simp only [PairingProbability,←Nat.card_eq_fintype_card]

theorem actual_simple_probability_even_upper (k j : ℕ) :
    SimpleProbability k ≤ PartialMoment k (2*j) := by
  rw [actual_simple_probability_indicator_average,actual_partial_moment_average]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun p _ => actual_simple_indicator_even_upper p j)

theorem actual_simple_probability_odd_lower (k j : ℕ) :
    PartialMoment k (2*j+1) ≤ SimpleProbability k := by
  rw [actual_simple_probability_indicator_average,actual_partial_moment_average]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun p _ => actual_simple_indicator_odd_lower p j)

theorem actual_partial_moment_limit (t : ℕ) :
    Tendsto (fun k : ℕ => PartialMoment k t) atTop (𝓝 (PartialPoisson t)) := by
  have h := tendsto_finsetSum (Finset.range (t+1)) (fun q _ =>
    ((actual_bad_descending_moment_limit q).div_const (q.factorial : ℝ)).const_mul
      ((-1 : ℝ)^q))
  have hc : (∑ q ∈ Finset.range (t+1),(-1 : ℝ)^q*((2 : ℝ)^q/(q.factorial : ℝ))) =
      PartialPoisson t := by
    unfold PartialPoisson
    apply Finset.sum_congr rfl
    intro q _
    rw [←mul_div_assoc,←mul_pow]
    norm_num
  rw [hc] at h
  exact h

#print axioms actual_partial_moment_average
#print axioms actual_simple_probability_indicator_average
#print axioms actual_simple_probability_even_upper
#print axioms actual_simple_probability_odd_lower
#print axioms actual_partial_moment_limit
end Reference.MD06SimplicityExponential
