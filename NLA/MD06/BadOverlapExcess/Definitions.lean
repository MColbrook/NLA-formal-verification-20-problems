module

public import NLA.MD06.JointSupportCounts.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadOverlap
open Reference.MD06CubicConfiguration Reference.MD06BadJointMoments
attribute [local instance] Classical.propDecidable

def OrientedEdge {n : ℕ} (x y : Dart n) : Dart n × Dart n :=
  if DartLT x y then (x,y) else (y,x)

def PartnerEdges {n : ℕ} (p : Pairing n) (u : Fin n) (S : Finset (Fin 3)) :
    Finset (Dart n × Dart n) :=
  S.image (fun a => OrientedEdge (u,a) (p.val (u,a)))

end Reference.MD06BadOverlap
