module

public import NLA.MD06.SpectralProbability.Definitions
public import NLA.MD06.CenteredMarkovDecay.PowerDecay
public import NLA.MD06.FiniteProbability.Definitions
public import Mathlib.Data.Nat.Log

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06SpectralProbability
open Reference.RootMD06SpectralTrace Reference.RootMD06CenteredMarkov
open Reference.MD06FiniteProbability Filter
open scoped Topology


theorem actual_sample_trace_scale_bounds (k : ℕ) :
    2 ^ TraceScale k ≤ Size k ∧ Size k ≤ 2 ^ (TraceScale k + 1) := by
  constructor
  · exact Nat.pow_log_le_self 2 (by dsimp [Size]; omega)
  · exact (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Size k)).le

theorem actual_sample_trace_scale_real_bounds (k : ℕ) :
    (2 : ℝ) ^ TraceScale k ≤ (Size k : ℝ) ∧ (Size k : ℝ) ≤ (2 : ℝ) ^ (TraceScale k + 1) := by
  exact_mod_cast actual_sample_trace_scale_bounds k

theorem actual_sample_trace_scale_tendsto_atTop : Tendsto TraceScale atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (2 ^ b)] with k hk
  apply Nat.le_log_of_pow_le (by norm_num : 1 < 2)
  dsimp [Size]
  omega

theorem actual_sample_quartic_trace_envelope_tendsto_zero :
    Tendsto (fun k : ℕ => (10804 * ((TraceScale k : ℝ) + 1) ^ 4 + 6) *
      (8 / GapRoot ^ 4) ^ TraceScale k) atTop (𝓝 0) := by
  have h := (actual_dyadic_polynomial_trace_envelope_tendsto_zero 4 10804 3).comp
    actual_sample_trace_scale_tendsto_atTop
  simpa only [Function.comp_def, show (2 : ℝ) * 3 = 6 by norm_num] using h

#print axioms actual_sample_trace_scale_bounds
#print axioms actual_sample_trace_scale_real_bounds
#print axioms actual_sample_trace_scale_tendsto_atTop
#print axioms actual_sample_quartic_trace_envelope_tendsto_zero
end Reference.RootMD06SpectralProbability
