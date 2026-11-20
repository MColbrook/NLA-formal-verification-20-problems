module

public import NLA.PF02.Normalization.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder
abbrev FactorPair (p q k : ℕ) := (Fin p → Mat (Fin k)) × (Fin q → Mat (Fin k))
def normalizedFactorSet {p q k : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) : Set (FactorPair p q k) :=
  {F | (∀ i, (F.1 i).PosSemidef) ∧ (∀ j, (F.2 j).PosSemidef) ∧
    rowSum F.1 = 1 ∧ ∀ i j, Matrix.trace (F.1 i * F.2 j) = M i j}
end Reference.PF02Normalization
