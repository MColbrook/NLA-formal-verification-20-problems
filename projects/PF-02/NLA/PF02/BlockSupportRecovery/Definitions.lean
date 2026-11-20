module

public import NLA.PF02.BlockConstruction.EnumeratedDefinitions
public import NLA.PF02.SupportBridge.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02BlockSupportRecovery
open Matrix NLA.PF02.Paper Reference.PF02BlockConstruction
open scoped BigOperators

def blockRows {r : ℕ} (A : Fin (Fintype.card (BlockIndex r)) →
    Matrix (Fin (3+r)) (Fin (3+r)) ℝ) (p : BlockIndex r) : Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  A (Fintype.equivFin (BlockIndex r) p)

def trailingSum {r : ℕ} (B : Fin (Fintype.card (BlockIndex r)) →
    Matrix (Fin (3+r)) (Fin (3+r)) ℝ) : Matrix (Fin (3+r)) (Fin (3+r)) ℝ :=
  ∑ p : SymIndex r, blockRows B (Sum.inr (Sum.inl p))

end Reference.PF02BlockSupportRecovery
