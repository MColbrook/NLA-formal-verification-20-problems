module

public import PaperDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace IV04.Paper

/-- Independent rational endpoints for every actual matrix entry. -/
structure RationalMatrixBox (n : ℕ) where
  lower : Matrix (Fin n) (Fin n) ℚ
  upper : Matrix (Fin n) (Fin n) ℚ
  ordered : ∀ i j, lower i j ≤ upper i j

def RationalMatrixBox.realizations {n : ℕ} (B : RationalMatrixBox n) : Set (Mat n) :=
  {A | ∀ i j, (B.lower i j : ℝ) ≤ A i j ∧ A i j ≤ (B.upper i j : ℝ)}

end IV04.Paper
