module

public import NLA.MD06.CyclePairPatterns.Definitions
public import Mathlib.Data.Fintype.CardEmbedding

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CyclePairPatterns
open Reference.MD06CubicConfiguration Reference.MD06FiniteProbability Reference.MD06PairingCounts
open scoped BigOperators
attribute [local instance] Classical.propDecidable

noncomputable def RawCycleCount (n ell : ℕ) (p : Pairing n) : ℕ :=
  Fintype.card {D : CycleData n ell // Matches (CyclePattern D) p}

noncomputable def MeanOrientedCycles (k ell : ℕ) : ℝ :=
  (∑ p : Pairing (Size k), (RawCycleCount (Size k) ell p : ℝ)) /
    Fintype.card (Pairing (Size k))

end Reference.MD06CyclePairPatterns