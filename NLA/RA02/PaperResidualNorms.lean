module

public import NLA.RA02.PaperResidualDefinitions
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.RA02.Paper

theorem residual_frobenius_squared_norm {n s : ℕ} (rows cols : Fin s ↪ Fin n) (t : ℝ) :
    paperFrobeniusSquared rows cols t =
      ‖(WithLp.toLp 2 (fun p : Fin n × Fin n => interpolatoryResidual (sharpFamily n t) rows cols p.1 p.2) :
        EuclideanSpace ℝ (Fin n × Fin n))‖^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i, ∑ j, (interpolatoryResidual (sharpFamily n t) rows cols i j)^2) =
    ∑ p : Fin n × Fin n, ‖interpolatoryResidual (sharpFamily n t) rows cols p.1 p.2‖^2
  rw [Fintype.sum_prod_type]
  simp only [Real.norm_eq_abs, sq_abs]

#print axioms residual_frobenius_squared_norm
end NLA.RA02.Paper
