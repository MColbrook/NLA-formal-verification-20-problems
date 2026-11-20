module

public import NLA.PF02.PaperSymmetricDeterminant

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.PF02.Paper

theorem paper_symmetric_space (n : ℕ) (X : Matrix (Fin n) (Fin n) ℝ) :
    X ∈ symmetricSpace n ℝ ↔ X.transpose = X := by
  rfl

theorem paper_congruence_action (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ)
    (X : symmetricSpace n ℝ) :
    (symmetricCongruence S X).val = S.transpose * X.val * S := by
  rfl

theorem paper_congruence_determinant (n : ℕ) (S : Matrix (Fin n) (Fin n) ℝ) :
    LinearMap.det (symmetricCongruence S) = S.det^(n+1) := by
  exact symmetricCongruence_det S

end NLA.PF02.Paper
