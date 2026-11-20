module

public import NLA.MD06.BoundedExcessPatterns.EventDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06BoundedExcess
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
attribute [local instance] Classical.propDecidable
def SimpleExcessNumerator (k K : ℕ) : ℝ :=
  PairingProbability (Size k) (fun p => IsSimplePairing p ∧ HasBoundedExcess K p)
def SimpleExcessProbability (k K : ℕ) : ℝ :=
  SimpleExcessNumerator k K/PairingProbability (Size k) IsSimplePairing
end Reference.MD06BoundedExcess
