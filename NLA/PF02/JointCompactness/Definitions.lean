module

public import NLA.PF02.Normalization.CompactDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02JointCompactness
open Matrix Reference.PF02Support Reference.PF02Normalization
open scoped BigOperators MatrixOrder

def normalizedConstraintSet {p q k : ℕ} :
    Set (Matrix (Fin p) (Fin q) ℝ × FactorPair p q k) :=
  {Z | Z.2 ∈ normalizedFactorSet Z.1}

def jointNormalizedFactorSet {p q k : ℕ} (M : ℝ → Matrix (Fin p) (Fin q) ℝ)
    (a b : ℝ) : Set (ℝ × FactorPair p q k) :=
  {Z | Z.1 ∈ Set.Icc a b ∧ Z.2 ∈ normalizedFactorSet (M Z.1)}

def perturbedGram {p k : ℕ} (F : Fin p → Mat (Fin k)) (η : ℝ) : Mat (Fin p) :=
  fun i j => Matrix.trace ((F i + η • (1 : Mat (Fin k))) *
    (F j + η • (1 : Mat (Fin k))))
end Reference.PF02JointCompactness
