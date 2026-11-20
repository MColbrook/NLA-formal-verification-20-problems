module

public import NLA.MF05.PaperCyclicConclusions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF05.Paper.Cyclic

theorem paper_literal_perturbation (n : ℕ) (δ : ℝ) :
    perturbation n δ = shift n + δ • corner n := by
  exact perturbation_literal n δ

theorem paper_nilpotent_shift (n : ℕ) : shift n ^ (n+1) = 0 := by
  exact shift_nilpotent n

theorem paper_shift_radius (n : ℕ) : realRadius {shift n} = 0 := by
  exact shift_radius_zero n

theorem paper_perturbation_radius (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    realRadius {perturbation n δ} = δ ^ (1 / ((n+1 : ℕ) : ℝ)) := by
  exact perturbation_radius_delta n δ hδ

theorem paper_hausdorff_distance (n : ℕ) (δ : ℝ) :
    realHausdorff {shift n} {perturbation n δ} = |δ| := by
  exact perturbation_distance n δ

theorem paper_perturbation_norm (n : ℕ) (δ : ℝ) (hδ : |δ| ≤ 1) :
    realSpectralNorm (perturbation n δ) ≤ 1 := by
  exact perturbation_norm_le_one n δ hδ

theorem paper_shift_norm (n : ℕ) : realSpectralNorm (shift n) ≤ 1 := by
  exact shift_norm_le_one n

theorem paper_characteristic_polynomial (n : ℕ) (δ : ℝ) :
    (perturbation n δ).charpoly = Polynomial.X^(n+1) - Polynomial.C δ := by
  exact perturbation_charpoly n δ

theorem paper_exponent_obstruction (n : ℕ) (α C ε : ℝ)
    (hα : 1 / ((n+1 : ℕ) : ℝ) < α) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      realHausdorff {shift n} {perturbation n δ} < ε ∧
      C * (realHausdorff {shift n} {perturbation n δ}) ^ α <
        |realRadius {perturbation n δ} - realRadius {shift n}| := by
  exact exponent_obstruction n α C ε hα hε

theorem paper_local_lipschitz_obstruction (n : ℕ) (hn : 1 ≤ n) (C ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      realHausdorff {shift n} {perturbation n δ} < ε ∧
      C * realHausdorff {shift n} {perturbation n δ} <
        |realRadius {perturbation n δ} - realRadius {shift n}| := by
  exact local_lipschitz_obstruction n hn C ε hε

end NLA.MF05.Paper.Cyclic
