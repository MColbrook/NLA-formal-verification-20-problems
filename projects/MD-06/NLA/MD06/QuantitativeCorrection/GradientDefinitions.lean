module

public import NLA.MD06.QuantitativeCorrection.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open WithLp
def GradientVector {n : ℕ} (G : SimpleGraph (Fin n)) (phi : Configuration n) : Configuration n :=
  toLp 2 (fun i => Reference.MD06Actual.Gradient G
    (Reference.MD06Actual.PhaseLift (fun a => phi a)) i)
end Reference.MD06Correction
