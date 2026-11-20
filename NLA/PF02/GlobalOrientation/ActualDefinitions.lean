module

public import NLA.PF02.GlobalOrientation.Definitions
public import NLA.PF02.BlockSupportRecovery.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02GlobalOrientation
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction Reference.PF02BlockSupportRecovery

def leadingRows {r : ℕ} (A : Fin (Fintype.card (BlockIndex r)) → Matrix (Fin (3+r)) (Fin (3+r)) ℝ) :
    SymIndex 3 → Matrix (Fin (3+r)) (Fin (3+r)) ℝ := fun p => blockRows A (Sum.inl p)

end Reference.PF02GlobalOrientation
