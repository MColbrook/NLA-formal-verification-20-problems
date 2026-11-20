module

public import NLA.MD06.BadJointMoments.OrderDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06JointSupportCounts
open Reference.MD06CubicConfiguration
attribute [local instance] Classical.propDecidable

def DartSupport {n : ℕ} (C : Finset (Dart n × Dart n)) : Finset (Dart n) :=
  C.biUnion (fun e => {e.1,e.2})

def VertexSupport {n : ℕ} (C : Finset (Dart n × Dart n)) : Finset (Fin n) :=
  (DartSupport C).image Prod.fst

def LocalSupport {n : ℕ} (C : Finset (Dart n × Dart n)) (u : Fin n) : Finset (Fin 3) :=
  Finset.univ.filter (fun a => (u,a) ∈ DartSupport C)

end Reference.MD06JointSupportCounts
