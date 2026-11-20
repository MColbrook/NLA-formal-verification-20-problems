module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
The actual spectral masks used in main.tex are genuine orthogonal projectors.
Extends the checked real MI-13 proof at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.OptimalityEquality.ProjectorRanks

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage
open scoped Matrix

theorem orthogonal_indicator_projector_idempotent {m : ℕ}
    (V : Square m) (hV : IsOrthogonal V) (p : Fin m → Prop) [DecidablePred p] :
    let P := V * Matrix.diagonal (fun i => if p i then (1 : ℝ) else 0) * V.transpose
    P * P = P := by
  let D := Matrix.diagonal (fun i => if p i then (1 : ℝ) else 0)
  have hD : D*D = D := by
    dsimp [D]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : p i <;> simp [hi]
  change (V*D*V.transpose)*(V*D*V.transpose) = V*D*V.transpose
  calc
    _ = V * D * (V.transpose*V) * D * V.transpose := by simp only [Matrix.mul_assoc]
    _ = V * (D*D) * V.transpose := by rw [hV.1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = V*D*V.transpose := by rw [hD]

theorem actual_left_spectral_projectors_symmetric_idempotent {m n : ℕ}
    (A : Rect m n) (tau : ℝ) :
    (leftAboveProjector A tau).transpose = leftAboveProjector A tau ∧
    leftAboveProjector A tau * leftAboveProjector A tau = leftAboveProjector A tau ∧
    (leftBoundaryProjector A tau).transpose = leftBoundaryProjector A tau ∧
    leftBoundaryProjector A tau * leftBoundaryProjector A tau = leftBoundaryProjector A tau := by
  classical
  refine ⟨leftAboveProjector_transpose A tau, ?_, ?_, ?_⟩
  · exact orthogonal_indicator_projector_idempotent (leftVectorMatrix A)
      (leftVectorMatrix_orthogonal A) (fun i => tau < singularValue A.transpose i.val)
  · simp only [leftBoundaryProjector, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  · exact orthogonal_indicator_projector_idempotent (leftVectorMatrix A)
      (leftVectorMatrix_orthogonal A) (fun i => singularValue A.transpose i.val = tau)

#print axioms actual_left_spectral_projectors_symmetric_idempotent
end
end Reference.RealOptimalityEquality
