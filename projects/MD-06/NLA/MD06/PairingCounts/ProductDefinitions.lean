module

public import NLA.MD06.PairingCounts.PatternDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06PairingCounts
open Reference.MD06CubicConfiguration
open scoped BigOperators

def PairingDenominator (n t : ℕ) : ℕ :=
  ∏ i ∈ Finset.range t, (3*n-2*i-1)

end Reference.MD06PairingCounts