module

public import NLA.PF02.GlobalOrientation.SignDefinitions
public import NLA.PF02.JointCompactness.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02GlobalOrientation Reference.PF02BlockConstruction Reference.PF02Normalization

def orthogonalSet (k : ℕ) : Set (Matrix (Fin k) (Fin k) ℝ) := {O | O * O.transpose = 1}

def perturbedBlockGram (r : ℕ) (η : ℝ) :
    Matrix (Fin (Fintype.card (BlockIndex r))) (Fin (Fintype.card (BlockIndex r))) ℝ :=
  Reference.PF02JointCompactness.perturbedGram (enumeratedFactor r) η

def normalizedOrientationProduct {r : ℕ}
    (F : FactorPair (Fintype.card (BlockIndex r)) (Fintype.card (BlockIndex r)) (3+r))
    (O : Matrix (Fin (3+r)) (Fin (3+r)) ℝ) : ℝ :=
  orientationPolynomial (leadingRows F.1) *
    orientationPolynomial (fun p => O.transpose * leadingRows F.1 p * O)

end Reference.PF02UniformPositiveOrientation
