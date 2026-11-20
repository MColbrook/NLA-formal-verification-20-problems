module

public import NLA.MD06.CanonicalCyclePatterns.FiberDefinitions
public import NLA.MD06.JointSupportCounts.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06SupportedCanonicalCycles
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

abbrev SupportedRawCycle {n : ℕ} (S : Finset (Fin n)) (ell : ℕ) :=
  {D : CycleData n ell // ∀i : Fin ell,D.1 i∈S}

abbrev SupportedCanonicalCycle {n : ℕ} (S : Finset (Fin n)) (ell : ℕ) :=
  {C : CanonicalCycleDatum n ell // VertexSupport C.val⊆S}

end Reference.MD06SupportedCanonicalCycles
