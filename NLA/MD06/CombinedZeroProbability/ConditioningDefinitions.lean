module

public import NLA.MD06.CombinedZeroProbability.Definitions
public import NLA.MD06.CanonicalCyclePatterns.MeanDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedZero
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open Reference.MD06CanonicalCyclePatterns
attribute [local instance] Classical.propDecidable
def SimpleNoCycleProbability (k ell : ℕ) : ℝ :=
  PairingProbability (Size k) (fun p =>
    IsSimplePairing p ∧ CanonicalCycleCount (Size k) ell p=0)/
      PairingProbability (Size k) IsSimplePairing
end Reference.MD06CombinedZero
