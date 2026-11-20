module

public import NLA.MD06.BadJointMoments.Definitions

@[expose] public section

set_option autoImplicit false
namespace Reference.MD06BadJointMoments
open Reference.MD06CubicConfiguration

def DartLT {n : ℕ} (x y : Dart n) : Prop :=
  x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2

end Reference.MD06BadJointMoments
