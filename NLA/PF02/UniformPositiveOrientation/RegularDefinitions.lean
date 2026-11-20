module

public import NLA.PF02.UniformPositiveOrientation.PerturbationDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02Normalization Reference.PF02BlockConstruction

def regularParameter (r : ℕ) (η : ℝ) : Prop :=
  (perturbedBlockGram r η).rank = (3+r)*(3+r+1)/2 ∧
  ∀ F : FactorPair (Fintype.card (BlockIndex r)) (Fintype.card (BlockIndex r)) (3+r),
    F ∈ normalizedFactorSet (k := 3+r) (perturbedBlockGram r η) →
    ∀ O : Matrix (Fin (3+r)) (Fin (3+r)) ℝ, O ∈ orthogonalSet (3+r) →
      0 < normalizedOrientationProduct (r := r) F O
end Reference.PF02UniformPositiveOrientation
