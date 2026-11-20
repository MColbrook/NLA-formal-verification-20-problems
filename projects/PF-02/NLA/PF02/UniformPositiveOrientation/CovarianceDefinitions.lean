module

public import NLA.PF02.UniformPositiveOrientation.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02Normalization Reference.PF02Support

def normalizingCongruence {p k : ℕ} (A C : Fin p → Mat (Fin k)) (S : Mat (Fin k)) : Mat (Fin k) :=
  rootSum A * S * (rootSum C)⁻¹

end Reference.PF02UniformPositiveOrientation
