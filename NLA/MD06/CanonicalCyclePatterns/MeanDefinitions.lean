module

public import NLA.MD06.CanonicalCyclePatterns.FiberDefinitions
public import NLA.MD06.CyclePairPatterns.CountDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability
open Reference.MD06CyclePairPatterns Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

def CanonicalCycleCount (n ell : ℕ) (p : Pairing n) : ℕ :=
  Nat.card {C : CanonicalCycleDatum n ell // Matches C.val p}

def MeanCanonicalCycles (k ell : ℕ) : ℝ :=
  (∑ p : Pairing (Size k), (CanonicalCycleCount (Size k) ell p : ℝ)) /
    (Fintype.card (Pairing (Size k)) : ℝ)

end Reference.MD06CanonicalCyclePatterns
