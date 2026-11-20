module

public import NLA.MD06.CyclePairPatterns.Definitions
public import NLA.MD06.BadOverlapExcess.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns Reference.MD06BadOverlap

def CanonicalConstraints {n : ℕ} (C : Finset (Dart n × Dart n)) :
    Finset (Dart n × Dart n) := C.image (fun e => OrientedEdge e.1 e.2)

def CanonicalCyclePattern {n ell : ℕ} (D : CycleData n ell) :
    Finset (Dart n × Dart n) := CanonicalConstraints (CyclePattern D)

abbrev CanonicalCycleDatum (n ell : ℕ) :=
  {C : Finset (Dart n × Dart n) // ∃D : CycleData n ell,CanonicalCyclePattern D=C}
end Reference.MD06CanonicalCyclePatterns
