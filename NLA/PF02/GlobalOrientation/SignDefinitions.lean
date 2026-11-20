module

public import NLA.PF02.GlobalOrientation.WitnessDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Reference.PF02BlockConstruction

def fiberSign {r : ℕ} (F : NLA.PF02.Factorization (enumeratedRealGram r) (3+r)) : Bool :=
  decide (0 < orientationPolynomial (leadingRows F.val.1))

end Reference.PF02GlobalOrientation
