module

public import NLA.PF02.UniformPositiveOrientation.WitnessDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02BlockConstruction

def enumeratedIntegerFactor (r : ℕ) (i : Fin (Fintype.card (BlockIndex r))) :
    Matrix (Fin (3+r)) (Fin (3+r)) ℤ :=
  finiteBlockFactorInt r ((Fintype.equivFin (BlockIndex r)).symm i)

def rationalPerturbedGram (r : ℕ) (q : ℚ) :
    Matrix (Fin (Fintype.card (BlockIndex r))) (Fin (Fintype.card (BlockIndex r))) ℚ :=
  fun i j => (enumeratedIntegerGram r i j : ℚ) +
    q * ((enumeratedIntegerFactor r i).trace : ℚ) +
    q * ((enumeratedIntegerFactor r j).trace : ℚ) + q^2 * (3+r)
end Reference.PF02UniformPositiveOrientation
