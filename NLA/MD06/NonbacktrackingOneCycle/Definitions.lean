module

public import NLA.MD06.NonbacktrackingWalkExposure.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06OneCycle
open Reference.MD06CubicConfiguration Reference.MD06PairingCounts
attribute [local instance] Classical.propDecidable

def UsedPorts {n : ℕ} (C : Finset (Dart n × Dart n)) (v : Fin n) : Finset (Dart n) :=
  (UsedDarts C).filter (fun a=>a.1=v)

end Reference.MD06OneCycle
