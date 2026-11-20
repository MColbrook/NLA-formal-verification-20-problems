module

public import NLA.MD06.SpectralProbability.TraceEnvelope
public import NLA.MD06.SimplicityExponentialLimit.ExpLimits
public import NLA.MD06.CubicConfiguration.PairingMeasure

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06SpectralProbability
open Reference.RootMD06SpectralTrace Reference.RootMD06CenteredMarkov
open Reference.MD06FiniteProbability Reference.MD06CubicConfiguration
open Reference.MD06Spectral Reference.MD06WalkExposure Reference.MD06SimplicityExponential Filter
open scoped Topology

theorem actual_simple_pairing_probability_limit :
    Tendsto (fun k : ℕ => PairingProbability (Size k) IsSimplePairing) atTop (𝓝 (Real.exp (-2))) := by
  have h := actual_simple_pairing_probability_exponential_limit
  change Tendsto (fun k : ℕ => ((UniformPairing k).toOuterMeasure {p | IsSimplePairing p}).toReal)
    atTop (𝓝 (Real.exp (-2))) at h
  simpa only [actual_pairing_probability_uniform_real] using h

theorem actual_conditioned_small_sorted_gap_envelope (k : ℕ) (hk : 6 ≤ TraceScale k) :
    ConditionedGraphProbability (Size k) (fun G =>
      LaplacianGap G (by dsimp [Size]; omega) < 1 / 10) ≤
      ((10804 * ((TraceScale k : ℝ) + 1) ^ 4 + 6) * (8 / GapRoot ^ 4) ^ TraceScale k) /
        PairingProbability (Size k) IsSimplePairing := by
  have hs : 0 < PairingProbability (Size k) IsSimplePairing := by
    have h := actual_uniform_pairing_simple_probability_positive k
    rwa [actual_pairing_probability_uniform_real] at h
  have hb := actual_conditioned_small_sorted_gap_probability_bound k (2 * TraceScale k)
    (by dsimp [Size]; omega) hs
  have he : 2 * (2 * TraceScale k) = 4 * TraceScale k := by omega
  rw [he] at hb
  calc
    _ ≤ (MeanNonbacktrackingTrace (Size k) (4 * TraceScale k) - (2 : ℝ) ^ (4 * TraceScale k) +
        2 * Size k * (2 : ℝ) ^ (2 * TraceScale k)) /
          (PairingProbability (Size k) IsSimplePairing * GapRoot ^ (4 * TraceScale k)) := hb
    _ = ((MeanNonbacktrackingTrace (Size k) (4 * TraceScale k) - (2 : ℝ) ^ (4 * TraceScale k) +
        2 * Size k * (2 : ℝ) ^ (2 * TraceScale k)) / GapRoot ^ (4 * TraceScale k)) /
          PairingProbability (Size k) IsSimplePairing := by rw [div_div]; congr 1; ring
    _ ≤ _ := div_le_div_of_nonneg_right (actual_centered_trace_normalized_envelope k hk) hs.le

theorem actual_conditioned_small_sorted_gap_probability_tendsto_zero :
    Tendsto (fun k : ℕ => ConditionedGraphProbability (Size k) (fun G =>
      LaplacianGap G (by dsimp [Size]; omega) < 1 / 10)) atTop (𝓝 0) := by
  have he := actual_sample_quartic_trace_envelope_tendsto_zero.div
    actual_simple_pairing_probability_limit (ne_of_gt (Real.exp_pos (-2)))
  simp only [zero_div] at he
  apply squeeze_zero' ?_ ?_ he
  · exact Filter.Eventually.of_forall (fun k => by
      unfold ConditionedGraphProbability PairingProbability
      positivity)
  · filter_upwards [actual_sample_trace_scale_tendsto_atTop.eventually (eventually_ge_atTop 6)] with k hk
    exact actual_conditioned_small_sorted_gap_envelope k hk

theorem actual_uniform_graph_small_sorted_gap_probability_tendsto_zero :
    Tendsto (fun k : ℕ => GraphProbability k (fun G =>
      LaplacianGap G (by dsimp [Size]; omega) < 1 / 10)) atTop (𝓝 0) := by
  simpa only [actual_configuration_conditioned_uniform_graph_law] using
    actual_conditioned_small_sorted_gap_probability_tendsto_zero

theorem actual_uniform_graph_sorted_gap_probability_tendsto_one :
    Tendsto (fun k : ℕ => GraphProbability k (fun G =>
      1 / 10 ≤ LaplacianGap G (by dsimp [Size]; omega))) atTop (𝓝 1) := by
  have h : Tendsto (fun k : ℕ => 1 - GraphProbability k (fun G =>
      LaplacianGap G (by dsimp [Size]; omega) < 1 / 10)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub actual_uniform_graph_small_sorted_gap_probability_tendsto_zero
  convert h using 1
  funext k
  simpa only [not_lt] using (actual_graph_probability_complement k
    (fun G => LaplacianGap G (by dsimp [Size]; omega) < 1 / 10))

theorem actual_uniform_cubic_sorted_gap_mass_tendsto_one :
    Tendsto (fun k : ℕ => ((UniformCubic k).toOuterMeasure {G : CubicSample k |
      1 / 10 ≤ LaplacianGap G.val (by dsimp [Size]; omega)}).toReal) atTop (𝓝 1) := by
  have heq : (fun k : ℕ => ((UniformCubic k).toOuterMeasure {G : CubicSample k |
      1 / 10 ≤ LaplacianGap G.val (by dsimp [Size]; omega)}).toReal) =
      (fun k : ℕ => GraphProbability k (fun G =>
        1 / 10 ≤ LaplacianGap G (by dsimp [Size]; omega))) := by
    funext k
    exact actual_graph_probability_uniform_real k (fun G =>
      1 / 10 ≤ LaplacianGap G (by dsimp [Size]; omega))
  rw [heq]
  exact actual_uniform_graph_sorted_gap_probability_tendsto_one

#print axioms actual_simple_pairing_probability_limit
#print axioms actual_conditioned_small_sorted_gap_envelope
#print axioms actual_conditioned_small_sorted_gap_probability_tendsto_zero
#print axioms actual_uniform_graph_small_sorted_gap_probability_tendsto_zero
#print axioms actual_uniform_graph_sorted_gap_probability_tendsto_one
#print axioms actual_uniform_cubic_sorted_gap_mass_tendsto_one
end Reference.RootMD06SpectralProbability
