module

public import NLA.PF02.UniformPositiveOrientation.PerturbationDefinitions
public import NLA.PF02.GlobalOrientation.WitnessDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization

def normalizedWitnessProduct (r : ℕ) (η : ℝ) : ℝ :=
  orientationPolynomial (leadingRows (r := r) (normalizedRow (shiftedFactors (enumeratedFactor r) η))) *
  orientationPolynomial (leadingRows (r := r) (normalizedRow (shiftedFactors (enumeratedReflectedFactor r) η)))
end Reference.PF02UniformPositiveOrientation
