module

public import NLA.MD06.CanonicalCycleOverlap.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCycleOverlap
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns
attribute [local instance] Classical.propDecidable

def FamilyUnion {n q : ℕ} (L : Fin q → ℕ) (D : ∀ i : Fin q, CycleData n (L i)) :
    Finset (Dart n × Dart n) :=
  Finset.univ.biUnion (fun i => CanonicalCyclePattern (D i))

end Reference.MD06CanonicalCycleOverlap
