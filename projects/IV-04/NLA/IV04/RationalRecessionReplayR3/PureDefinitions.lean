module

public import NLA.IV04.PolyhedronSupportReplayR3.PureDefinitions

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Matrix BigOperators
namespace Reference.IV04RationalRecessionRay
open Reference.IV04AffinePolyhedronSteps Reference.IV04OriginalObjectiveAttainment
def rowObjective {n : ℕ} (c : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun x := dotProduct c x
  map_add' := by intro x y; simp [dotProduct,mul_add,Finset.sum_add_distrib]
  map_smul' := by intro r x; simp [dotProduct,Finset.mul_sum,mul_left_comm]

def thresholdMatrix {ι : Type*} {n : ℕ} (A : Matrix ι (Fin n) ℚ)
    (c : Fin n → ℚ) : Matrix (ι ⊕ Unit) (Fin n) ℚ
  | Sum.inl i,j => A i j
  | Sum.inr _,j => -c j
def thresholdBounds {ι : Type*} (b : ι → ℚ) (k : ℚ) : ι ⊕ Unit → ℚ
  | Sum.inl i => b i
  | Sum.inr _ => -k
def thresholdDerivativeBounds {ι : Type*} : ι ⊕ Unit → ℚ
  | Sum.inl _ => 0
  | Sum.inr _ => -1

def integerThresholdMatrix {ι : Type*} {n : ℕ} (A : Matrix ι (Fin n) ℤ)
    (c : Fin n → ℤ) : Matrix (ι ⊕ Unit) (Fin n) ℤ
  | Sum.inl i,j => A i j
  | Sum.inr _,j => -c j
def integerThresholdDerivativeBounds {ι : Type*} : ι ⊕ Unit → ℤ
  | Sum.inl _ => 0
  | Sum.inr _ => -1

end Reference.IV04RationalRecessionRay
