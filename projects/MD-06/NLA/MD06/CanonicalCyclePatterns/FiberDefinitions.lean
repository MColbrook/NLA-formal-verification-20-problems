module

public import NLA.MD06.CanonicalCyclePatterns.SymmetryDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns

abbrev CycleFiber (n ell : ℕ) (C : Finset (Dart n × Dart n)) :=
  {D : CycleData n ell // CanonicalCyclePattern D=C}

end Reference.MD06CanonicalCyclePatterns
