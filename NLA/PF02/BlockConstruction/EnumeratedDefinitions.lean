module

public import NLA.PF02.BlockConstruction.Definitions
public import NLA.PF02.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockConstruction
open Matrix

def enumeratedIntegerGram (r : ℕ) :
    Matrix (Fin (Fintype.card (BlockIndex r))) (Fin (Fintype.card (BlockIndex r))) ℤ :=
  (finiteBlockGramInt r).reindex (Fintype.equivFin (BlockIndex r)) (Fintype.equivFin (BlockIndex r))

def enumeratedRealGram (r : ℕ) :
    Matrix (Fin (Fintype.card (BlockIndex r))) (Fin (Fintype.card (BlockIndex r))) ℝ :=
  (enumeratedIntegerGram r).map (Int.castRingHom ℝ)

def enumeratedFactor (r : ℕ) (i : Fin (Fintype.card (BlockIndex r))) :
    Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  finiteBlockFactor r ((Fintype.equivFin (BlockIndex r)).symm i)

end Reference.PF02BlockConstruction
