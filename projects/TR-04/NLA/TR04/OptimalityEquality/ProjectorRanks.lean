module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual projector ranks identify the paper's dimensions k=dim H and t=dim E.
Extends real MI-13/RA02 at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.OptimalityEquality.CountIdentity

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage
open scoped Matrix

theorem orthogonal_sandwich_rank {m : ℕ} (V D : Square m) (hV : IsOrthogonal V) :
    (V * D * V.transpose).rank = D.rank := by
  let P := V * D * V.transpose
  have hlow : D = V.transpose * P * V := by
    symm
    calc
      _ = (V.transpose * V) * D * (V.transpose * V) := by simp only [P, Matrix.mul_assoc]
      _ = D := by rw [hV.1]; simp
  have hup : P.rank ≤ D.rank :=
    (Matrix.rank_mul_le_left (V*D) V.transpose).trans (Matrix.rank_mul_le_right V D)
  have hdown : D.rank ≤ P.rank := by
    rw [hlow]
    exact (Matrix.rank_mul_le_left (V.transpose*P) V).trans
      (Matrix.rank_mul_le_right V.transpose P)
  exact le_antisymm hup hdown

theorem orthogonal_indicator_projector_rank {m : ℕ}
    (V : Square m) (hV : IsOrthogonal V) (p : Fin m → Prop) [DecidablePred p] :
    (V * Matrix.diagonal (fun i => if p i then (1 : ℝ) else 0) * V.transpose).rank =
      (Finset.univ.filter p).card := by
  rw [orthogonal_sandwich_rank V _ hV, Matrix.rank_diagonal]
  simp [Fintype.card_subtype]

theorem leftAboveProjector_rank_eq_multiplicity {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    (leftAboveProjector A tau).rank = aboveMultiplicity A tau := by
  classical
  exact orthogonal_indicator_projector_rank (leftVectorMatrix A)
    (leftVectorMatrix_orthogonal A) (fun i => tau < singularValue A.transpose i.val)

theorem leftBoundaryProjector_rank_eq_multiplicity {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    (leftBoundaryProjector A tau).rank = boundaryMultiplicity A tau := by
  classical
  exact orthogonal_indicator_projector_rank (leftVectorMatrix A)
    (leftVectorMatrix_orthogonal A) (fun i => singularValue A.transpose i.val = tau)

/-- Actual arbitrary optimal real-matrix residual form of main.tex
lem:tr04-equality. Projector ranks are genuine dimensions of H and E. -/
theorem actual_best_rank_residual_above_and_full_boundary {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r) (hrank : r < A.rank) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C)) :
    leftAboveProjector A (singularValue A (r-1)) * (A-B) = 0 ∧
      (r - (leftAboveProjector A (singularValue A (r-1))).rank =
        (leftBoundaryProjector A (singularValue A (r-1))).rank →
      (leftAboveProjector A (singularValue A (r-1)) +
        leftBoundaryProjector A (singularValue A (r-1))) * (A-B) = 0) := by
  refine ⟨left_above_annihilates_best_rank_residual_of_rank_gt A B r hr hrank hB hbest, ?_⟩
  intro hcount
  apply left_full_boundary_annihilates_best_rank_residual_of_paper_multiplicities A B r hr hrank hB hbest
  simpa only [leftAboveProjector_rank_eq_multiplicity,
    leftBoundaryProjector_rank_eq_multiplicity] using hcount

#print axioms leftAboveProjector_rank_eq_multiplicity
#print axioms leftBoundaryProjector_rank_eq_multiplicity
#print axioms actual_best_rank_residual_above_and_full_boundary
end
end Reference.RealOptimalityEquality
