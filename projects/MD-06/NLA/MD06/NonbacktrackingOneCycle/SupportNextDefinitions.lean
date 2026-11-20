module

public import NLA.MD06.NonbacktrackingOneCycle.Definitions
public import Mathlib.Dynamics.PeriodicPts.Defs

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts Reference.MD06WalkExposure
attribute [local instance] Classical.propDecidable

noncomputable def SupportedChoice {n : ℕ} (p : Pairing n) (C : Finset (Dart n × Dart n)) (a : Dart n) : Fin 2 :=
  if h : ∃ i : Fin 2,PortChoice (p.val a) i∈UsedDarts C then Classical.choose h else 0

noncomputable def SupportNext {n : ℕ} (p : Pairing n) (C : Finset (Dart n × Dart n)) (a : Dart n) : Dart n :=
  PortChoice (p.val a) (SupportedChoice p C a)

end Reference.MD06OneCycle
