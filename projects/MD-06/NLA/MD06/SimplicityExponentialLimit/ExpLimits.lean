module

public import NLA.MD06.SimplicityExponentialLimit.Averages
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06SimplicityExponential
open Filter Topology
open scoped BigOperators

theorem actual_double_offset_atTop (c : ℕ) :
    Tendsto (fun j : ℕ => 2*j+c) atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with j hj
  omega

theorem actual_partial_poisson_limit :
    Tendsto PartialPoisson atTop (𝓝 (Real.exp (-2))) := by
  have hs : HasSum (fun i : ℕ => (-2 : ℝ)^i/(i.factorial : ℝ)) (Real.exp (-2)) := by
    rw [Real.exp_eq_exp_ℝ,NormedSpace.exp_eq_tsum_div]
    exact (NormedSpace.expSeries_div_summable (-2 : ℝ)).hasSum
  have ha : Tendsto (fun t : ℕ => t+1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with t ht
    omega
  exact hs.tendsto_sum_nat.comp ha

theorem actual_simple_pairing_probability_exponential_limit :
    Tendsto SimpleProbability atTop (𝓝 (Real.exp (-2))) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hp := actual_partial_poisson_limit.comp (actual_double_offset_atTop 1)
    obtain ⟨j,hj⟩ := (hp.eventually (eventually_gt_nhds ha)).exists
    have hm := (actual_partial_moment_limit (2*j+1)).eventually
      (eventually_gt_nhds hj)
    exact hm.mono (fun k hk => lt_of_lt_of_le hk (actual_simple_probability_odd_lower k j))
  · intro a ha
    have hp := actual_partial_poisson_limit.comp (actual_double_offset_atTop 0)
    obtain ⟨j,hj⟩ := (hp.eventually (eventually_lt_nhds ha)).exists
    have hm := (actual_partial_moment_limit (2*j)).eventually
      (eventually_lt_nhds hj)
    exact hm.mono (fun k hk => lt_of_le_of_lt (actual_simple_probability_even_upper k j) hk)

#print axioms actual_double_offset_atTop
#print axioms actual_partial_poisson_limit
#print axioms actual_simple_pairing_probability_exponential_limit
end Reference.MD06SimplicityExponential
