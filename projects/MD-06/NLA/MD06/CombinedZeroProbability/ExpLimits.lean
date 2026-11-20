module

public import NLA.MD06.CombinedZeroProbability.Averages
public import NLA.MD06.SimplicityExponentialLimit.ExpLimits

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedZero
open Filter Topology

theorem actual_partial_exponential_limit (ell : ℕ) :
    Tendsto (PartialExponential ell) atTop
      (𝓝 (Real.exp (-(2+(2 : ℝ)^ell/(2*(ell : ℝ)))))) := by
  let x : ℝ := -(2+(2 : ℝ)^ell/(2*(ell : ℝ)))
  have hs : HasSum (fun i : ℕ => x^i/(i.factorial : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
    exact (NormedSpace.expSeries_div_summable x).hasSum
  have ha : Tendsto (fun t : ℕ => t+1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with t ht
    omega
  exact hs.tendsto_sum_nat.comp ha

theorem actual_combined_zero_probability_limit (ell : ℕ) (hell : 3≤ell) :
    Tendsto (fun k => ZeroProbability k ell) atTop
      (𝓝 (Real.exp (-(2+(2 : ℝ)^ell/(2*(ell : ℝ)))))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hp := (actual_partial_exponential_limit ell).comp
      (Reference.MD06SimplicityExponential.actual_double_offset_atTop 1)
    obtain ⟨j,hj⟩ := (hp.eventually (eventually_gt_nhds ha)).exists
    have hm := (actual_partial_moment_limit ell (2*j+1) hell).eventually
      (eventually_gt_nhds hj)
    exact hm.mono (fun k hk => lt_of_lt_of_le hk (actual_zero_probability_odd_lower k ell j))
  · intro a ha
    have hp := (actual_partial_exponential_limit ell).comp
      (Reference.MD06SimplicityExponential.actual_double_offset_atTop 0)
    obtain ⟨j,hj⟩ := (hp.eventually (eventually_lt_nhds ha)).exists
    have hm := (actual_partial_moment_limit ell (2*j) hell).eventually
      (eventually_lt_nhds hj)
    exact hm.mono (fun k hk => lt_of_le_of_lt (actual_zero_probability_even_upper k ell j) hk)

#print axioms actual_partial_exponential_limit
#print axioms actual_combined_zero_probability_limit
end Reference.MD06CombinedZero
