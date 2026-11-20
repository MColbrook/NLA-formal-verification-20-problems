module

public import NLA.MD06.CanonicalCyclePatterns.FirstMoment
public import NLA.MD06.CycleMoments.FirstLimits

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open Reference.MD06CyclePairPatterns Reference.MD06PairingCounts
open Filter Topology
attribute [local instance] Classical.propDecidable

theorem actual_mean_canonical_cycles_formula (k ell : ℕ) [NeZero ell] :
    MeanCanonicalCycles k ell =
      ((Size k).descFactorial ell : ℝ)*(6 : ℝ)^ell /
        ((2*(ell : ℝ))*(PairingDenominator (Size k) ell : ℝ)) := by
  rw [actual_mean_canonical_cycles,actual_mean_oriented_cycles_formula,div_div]
  rw [mul_comm (PairingDenominator (Size k) ell : ℝ)]

theorem actual_mean_canonical_cycles_limit (ell : ℕ) [NeZero ell] :
    Tendsto (fun k => MeanCanonicalCycles k ell) atTop
      (𝓝 ((2 : ℝ)^ell/(2*(ell : ℝ)))) := by
  simpa only [actual_mean_canonical_cycles] using
    (Reference.MD06CycleMoments.actual_mean_oriented_cycles_limit ell).div_const
      (2*(ell : ℝ))

#print axioms actual_mean_canonical_cycles_formula
#print axioms actual_mean_canonical_cycles_limit
end Reference.MD06CanonicalCyclePatterns
