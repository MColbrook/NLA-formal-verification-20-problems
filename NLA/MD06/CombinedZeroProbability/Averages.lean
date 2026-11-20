module

public import NLA.MD06.CombinedZeroProbability.Definitions
public import NLA.MD06.CombinedDescendingMoments.MeanLimits
public import NLA.MD06.SimplicityExponentialLimit.Pointwise

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedZero
open Reference.MD06CombinedMoments Reference.MD06MixedLowCycleBijections
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open Filter Topology
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_mean_choose_descending (k ell q : ℕ) :
    MeanDescending (Size k) q ell/(q.factorial : ℝ)=
      (∑p : Pairing (Size k),((MarkedMatchingCount (ell:=ell) p).choose q : ℝ))/
        (Fintype.card (Pairing (Size k)) : ℝ) := by
  have hq : (q.factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero q
  unfold MeanDescending
  rw [div_right_comm,Finset.sum_div]
  simp only [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  simp [hq]

theorem actual_partial_moment_average (k ell t : ℕ) :
    PartialMoment k ell t=
      (∑p : Pairing (Size k),∑i∈Finset.range (t+1),
        (-1 : ℝ)^i*((MarkedMatchingCount (ell:=ell) p).choose i : ℝ))/
          (Fintype.card (Pairing (Size k)) : ℝ) := by
  unfold PartialMoment
  simp_rw [actual_mean_choose_descending]
  simp_rw [←mul_div_assoc,Finset.mul_sum]
  rw [←Finset.sum_div,Finset.sum_comm]

theorem actual_zero_probability_indicator_average (k ell : ℕ) :
    ZeroProbability k ell=
      (∑p : Pairing (Size k),if MarkedMatchingCount (ell:=ell) p=0 then (1 : ℝ) else 0)/
        (Fintype.card (Pairing (Size k)) : ℝ) := by
  have h : (∑p : Pairing (Size k),if MarkedMatchingCount (ell:=ell) p=0 then (1 : ℝ) else 0)=
      (Fintype.card {p : Pairing (Size k) // MarkedMatchingCount (ell:=ell) p=0} : ℝ) := by
    rw [Fintype.card_subtype]
    simp
  rw [h]
  simp only [ZeroProbability,PairingProbability,←Nat.card_eq_fintype_card]

theorem actual_zero_probability_even_upper (k ell j : ℕ) :
    ZeroProbability k ell≤PartialMoment k ell (2*j) := by
  rw [actual_zero_probability_indicator_average,actual_partial_moment_average]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun p _ =>
    Reference.MD06SimplicityExponential.actual_bonferroni_even_upper
      (MarkedMatchingCount (ell:=ell) p) j)

theorem actual_zero_probability_odd_lower (k ell j : ℕ) :
    PartialMoment k ell (2*j+1)≤ZeroProbability k ell := by
  rw [actual_zero_probability_indicator_average,actual_partial_moment_average]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact Finset.sum_le_sum (fun p _ =>
    Reference.MD06SimplicityExponential.actual_bonferroni_odd_lower
      (MarkedMatchingCount (ell:=ell) p) j)

theorem actual_partial_moment_limit (ell t : ℕ) (hell : 3≤ell) :
    Tendsto (fun k => PartialMoment k ell t) atTop (𝓝 (PartialExponential ell t)) := by
  have h := tendsto_finsetSum (Finset.range (t+1)) (fun q _ =>
    ((actual_combined_descending_moment_limit q ell hell).div_const (q.factorial : ℝ)).const_mul
      ((-1 : ℝ)^q))
  have hc : (∑q∈Finset.range (t+1),(-1 : ℝ)^q*
      ((2+(2 : ℝ)^ell/(2*(ell : ℝ)))^q/(q.factorial : ℝ)))=PartialExponential ell t := by
    unfold PartialExponential
    apply Finset.sum_congr rfl
    intro q _
    rw [←mul_div_assoc,←mul_pow]
    congr 2
    ring
  rw [hc] at h
  exact h

#print axioms actual_mean_choose_descending
#print axioms actual_partial_moment_average
#print axioms actual_zero_probability_indicator_average
#print axioms actual_zero_probability_even_upper
#print axioms actual_zero_probability_odd_lower
#print axioms actual_partial_moment_limit
end Reference.MD06CombinedZero
