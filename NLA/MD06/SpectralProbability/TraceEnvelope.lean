module

public import NLA.MD06.SpectralProbability.DyadicRouting
public import NLA.MD06.DivisorTraceBound.Quantitative
public import NLA.MD06.CenteredMarkovDecay.Markov
public import NLA.MD06.NonbacktrackingOneCycle.TraceMean

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06SpectralProbability
open Reference.RootMD06SpectralTrace Reference.RootMD06CenteredMarkov Reference.RootMD06DivisorTrace
open Reference.MD06FiniteProbability Reference.MD06WalkExposure Reference.MD06OneCycle
open scoped BigOperators

theorem actual_centered_trace_upper_envelope (k : ℕ) (hk : 6 ≤ TraceScale k) :
    MeanNonbacktrackingTrace (Size k) (4 * TraceScale k) - (2 : ℝ) ^ (4 * TraceScale k) +
      2 * Size k * (2 : ℝ) ^ (2 * TraceScale k) ≤
      10804 * ((TraceScale k : ℝ) + 1) ^ 4 * (2 : ℝ) ^ (4 * TraceScale k) / (Size k : ℝ) +
        3 * Size k * (2 : ℝ) ^ (2 * TraceScale k) := by
  let s := TraceScale k
  have hnat := actual_sample_trace_scale_bounds k
  have hn : 2 * (4 * s) + 1 ≤ Size k :=
    (actual_dyadic_walk_length_admissible s hk).trans hnat.1
  have hm := actual_nonbacktracking_trace_mean_bound k (4 * s) (by omega) hn
  have hd := actual_dyadic_divisor_trace_sum_bound (Size k) s hk hnat.1
  have hc := actual_quartic_trace_error_combination (Size k) s
  change MeanNonbacktrackingTrace (Size k) (4 * s) ≤ DivisorTraceContribution (Size k) (4 * s) +
    27 * ((4 * s : ℕ) : ℝ) ^ 2 * ((4 * s + 1 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ (4 * s) / (Size k : ℝ) at hm
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at hm
  change MeanNonbacktrackingTrace (Size k) (4 * s) - (2 : ℝ) ^ (4 * s) +
    2 * Size k * (2 : ℝ) ^ (2 * s) ≤ _
  calc
    _ ≤ ((2 : ℝ) ^ (4 * s) + (4 * (s : ℝ)) * (2 : ℝ) ^ (4 * s) / (Size k : ℝ) +
        (Size k : ℝ) * (2 : ℝ) ^ (2 * s)) +
        27 * (4 * (s : ℝ)) ^ 2 * (4 * (s : ℝ) + 1) ^ 2 * (2 : ℝ) ^ (4 * s) / (Size k : ℝ) -
        (2 : ℝ) ^ (4 * s) + 2 * Size k * (2 : ℝ) ^ (2 * s) := by
          simp only [Size, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hm hd ⊢
          linarith
    _ = (27 * (4 * (s : ℝ)) ^ 2 * (4 * (s : ℝ) + 1) ^ 2 + 4 * (s : ℝ)) *
        (2 : ℝ) ^ (4 * s) / (Size k : ℝ) + 3 * Size k * (2 : ℝ) ^ (2 * s) := by ring
    _ ≤ _ := by change _ ≤ 10804 * ((s : ℝ) + 1) ^ 4 * (2 : ℝ) ^ (4 * s) / (Size k : ℝ) + _; linarith

theorem actual_centered_trace_normalized_envelope (k : ℕ) (hk : 6 ≤ TraceScale k) :
    (MeanNonbacktrackingTrace (Size k) (4 * TraceScale k) - (2 : ℝ) ^ (4 * TraceScale k) +
      2 * Size k * (2 : ℝ) ^ (2 * TraceScale k)) / GapRoot ^ (4 * TraceScale k) ≤
      (10804 * ((TraceScale k : ℝ) + 1) ^ 4 + 6) * (8 / GapRoot ^ 4) ^ TraceScale k := by
  have hp : 0 < GapRoot := by linarith [actual_gap_root_rational_bounds.1]
  have hb := actual_centered_trace_upper_envelope k hk
  have hn := actual_sample_trace_scale_real_bounds k
  have he := actual_dyadic_polynomial_trace_error_bound (TraceScale k) 4 (Size k) 10804 3
    hn.1 hn.2 (by norm_num) (by norm_num)
  have hb' := div_le_div_of_nonneg_right hb (pow_nonneg hp.le (4 * TraceScale k))
  have hid : (10804 * ((TraceScale k : ℝ) + 1) ^ 4 * (2 : ℝ) ^ (4 * TraceScale k) / (Size k : ℝ) +
      3 * Size k * (2 : ℝ) ^ (2 * TraceScale k)) / GapRoot ^ (4 * TraceScale k) =
    (10804 * ((TraceScale k : ℝ) + 1) ^ 4 * ((2 : ℝ) ^ (4 * TraceScale k) / (Size k : ℝ)) +
      3 * Size k * (2 : ℝ) ^ (2 * TraceScale k)) / GapRoot ^ (4 * TraceScale k) := by ring
  rw [hid] at hb'
  exact hb'.trans (by simpa only [show (2 : ℝ) * 3 = 6 by norm_num] using he)

#print axioms actual_centered_trace_upper_envelope
#print axioms actual_centered_trace_normalized_envelope
end Reference.RootMD06SpectralProbability
