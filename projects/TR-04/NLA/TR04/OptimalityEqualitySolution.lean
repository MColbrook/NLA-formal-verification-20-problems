module

public import NLA.TR04.PaperTensorEquality
public import NLA.TR04.OptimalityEquality.SpectralProjectors
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
open Reference.RealSVDPackage

theorem verified_leftBasis_gram {m n : ℕ} (A : Rect m n) :
    RectangularGramBasis A.transpose (leftBasis A) := by
  exact leftBasis_gram A

theorem verified_leftVectorMatrix_gram_diagonal {m n : ℕ} (A : Rect m n) :
    (leftVectorMatrix A).transpose * (A * A.transpose) * leftVectorMatrix A =
      Matrix.diagonal (fun i : Fin m => singularValue A.transpose i.val ^ 2) := by
  exact leftVectorMatrix_gram_diagonal A

theorem verified_singularValue_pos_iff_lt_rank {m n : ℕ} (A : Rect m n) (k : ℕ) :
    0 < singularValue A k ↔ k < A.rank := by
  exact singularValue_pos_iff_lt_rank A k

theorem verified_leftAboveProjector_rank_eq_multiplicity {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    (leftAboveProjector A tau).rank = aboveMultiplicity A tau := by
  exact leftAboveProjector_rank_eq_multiplicity A tau

theorem verified_leftBoundaryProjector_rank_eq_multiplicity {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    (leftBoundaryProjector A tau).rank = boundaryMultiplicity A tau := by
  exact leftBoundaryProjector_rank_eq_multiplicity A tau

theorem verified_actual_best_rank_residual_above_and_full_boundary {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r) (hrank : r < A.rank) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C)) :
    leftAboveProjector A (singularValue A (r-1)) * (A-B) = 0 ∧
      (r - (leftAboveProjector A (singularValue A (r-1))).rank =
        (leftBoundaryProjector A (singularValue A (r-1))).rank →
      (leftAboveProjector A (singularValue A (r-1)) +
        leftBoundaryProjector A (singularValue A (r-1))) * (A-B) = 0) := by
  exact actual_best_rank_residual_above_and_full_boundary A B r hr hrank hB hbest

theorem verified_actual_left_spectral_projectors_symmetric_idempotent {m n : ℕ}
    (A : Rect m n) (tau : ℝ) :
    (leftAboveProjector A tau).transpose = leftAboveProjector A tau ∧
    leftAboveProjector A tau * leftAboveProjector A tau = leftAboveProjector A tau ∧
    (leftBoundaryProjector A tau).transpose = leftBoundaryProjector A tau ∧
    leftBoundaryProjector A tau * leftBoundaryProjector A tau = leftBoundaryProjector A tau := by
  exact actual_left_spectral_projectors_symmetric_idempotent A tau

#print axioms Reference.RealOptimalityEquality.verified_leftBasis_gram
#print axioms Reference.RealOptimalityEquality.verified_leftVectorMatrix_gram_diagonal
#print axioms Reference.RealOptimalityEquality.verified_singularValue_pos_iff_lt_rank
#print axioms Reference.RealOptimalityEquality.verified_leftAboveProjector_rank_eq_multiplicity
#print axioms Reference.RealOptimalityEquality.verified_leftBoundaryProjector_rank_eq_multiplicity
#print axioms Reference.RealOptimalityEquality.verified_actual_best_rank_residual_above_and_full_boundary
#print axioms Reference.RealOptimalityEquality.verified_actual_left_spectral_projectors_symmetric_idempotent
end Reference.RealOptimalityEquality

namespace Reference.PaperTensorEquality
open Reference.RealSVDPackage Reference.RealOptimalityEquality

theorem verified_actual_tensor_first_unfolding_best_rank_residual {d : ℕ}
    (dimensions : Fin (d+1) → ℕ) (A Y : TensorIndex d dimensions → ℝ)
    (r : ℕ) (hr : 0 < r) (hrank : r < (actualFirstUnfolding dimensions A).rank)
    (hY : (actualFirstUnfolding dimensions Y).rank ≤ r)
    (hbest : ∀ C : Rect (dimensions 0) (Fintype.card (SuffixTensorIndex d dimensions)),
      C.rank ≤ r →
      frobeniusSq (actualFirstUnfolding dimensions A-actualFirstUnfolding dimensions Y) ≤
      frobeniusSq (actualFirstUnfolding dimensions A-C)) :
    let a := actualFirstUnfolding dimensions A
    let y := actualFirstUnfolding dimensions Y
    let tau := singularValue a (r-1)
    leftAboveProjector a tau * (a-y) = 0 ∧
      (r-(leftAboveProjector a tau).rank=(leftBoundaryProjector a tau).rank →
        (leftAboveProjector a tau+leftBoundaryProjector a tau) * (a-y)=0) := by
  exact actual_tensor_first_unfolding_best_rank_residual dimensions A Y r hr hrank hY hbest

#print axioms verified_actual_tensor_first_unfolding_best_rank_residual
end Reference.PaperTensorEquality
