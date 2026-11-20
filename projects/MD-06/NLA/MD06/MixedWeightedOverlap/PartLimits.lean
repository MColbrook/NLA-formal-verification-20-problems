module

public import NLA.MD06.MixedWeightedOverlap.PartCounts
public import NLA.MD06.WeightedOverlap.PartLimits

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedWeightedOverlap
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
open Reference.MD06FiniteProbability Reference.MD06WeightedOverlap
open Filter Topology

theorem actual_mixed_excess_part_mean_limit (q ell v e : ℕ) (hve : v<e) :
    Tendsto (fun k : ℕ => PartMean (Size k) q ell v e) atTop (𝓝 0) := by
  have h := (actual_excess_denominator_formula_limit v e hve).mul_const
    (((3*v+18*v^2+2^(9*v^2))^q : ℕ) : ℝ)
  simp only [zero_mul] at h
  have hr : Tendsto (fun k : ℕ =>
      ((Size k : ℝ)^v*((3*v+18*v^2+2^(9*v^2))^q : ℕ))/
        (PairingDenominator (Size k) e : ℝ)) atTop (𝓝 0) := by
    have hh := h.comp actual_size_tendsto_atTop
    convert hh using 1
    funext k
    simp only [Function.comp_apply]
    ring
  exact squeeze_zero (fun k => actual_mixed_part_mean_nonnegative (Size k) q ell v e)
    (fun k => actual_mixed_part_mean_finite_bound k q ell v e) hr

theorem actual_mixed_part_mean_all_shapes_limit (q ell v e : ℕ) :
    Tendsto (fun k : ℕ => PartMean (Size k) q ell v e) atTop (𝓝 0) := by
  by_cases hve : v<e
  · exact actual_mixed_excess_part_mean_limit q ell v e hve
  · have hz (k : ℕ) : PartMean (Size k) q ell v e=0 := by
      let : IsEmpty (PartDatum (Size k) q ell v e) :=
        ⟨fun F => hve (by have h := (actual_mixed_part_shape_bounds F).1;omega)⟩
      simp [PartMean,PartCount]
    simpa only [hz] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

#print axioms actual_mixed_excess_part_mean_limit
#print axioms actual_mixed_part_mean_all_shapes_limit
end Reference.MD06MixedWeightedOverlap
