module

public import NLA.PF02.UniformPositiveOrientation.CovarianceDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization

def shiftedFactors {p k : ℕ} (A : Fin p → Matrix (Fin k) (Fin k) ℝ) (η : ℝ)
    (i : Fin p) : Matrix (Fin k) (Fin k) ℝ := A i + η • 1

def normalizedFiberSign {r : ℕ} {η : ℝ}
    (F : NLA.PF02.Factorization (perturbedBlockGram r η) (3+r)) : Bool :=
  decide (0 < orientationPolynomial (leadingRows (r := r) (normalizedRow F.val.1)))

end Reference.PF02UniformPositiveOrientation
