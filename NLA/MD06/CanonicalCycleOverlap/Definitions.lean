module

public import NLA.MD06.CanonicalCyclePatterns.MeanDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCycleOverlap
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns
attribute [local instance] Classical.propDecidable

def CycleUnion {n ell ell' : ℕ} (D : CycleData n ell) (E : CycleData n ell') :
    Finset (Dart n × Dart n) := CanonicalCyclePattern D ∪ CanonicalCyclePattern E

end Reference.MD06CanonicalCycleOverlap
