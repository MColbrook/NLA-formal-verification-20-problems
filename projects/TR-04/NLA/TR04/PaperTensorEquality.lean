module

public import NLA.TR04.PaperTensorEqualityDefinitions
public import NLA.TR04.OptimalityEquality.SpectralProjectors
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.PaperTensorEquality
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality

/-- The paper equality lemma, applied to the actual first unfolding of dense
real tensors. The optimum compares with every actual real rank-r matrix. -/
theorem actual_tensor_first_unfolding_best_rank_residual {d : ℕ}
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
  exact actual_best_rank_residual_above_and_full_boundary
    (actualFirstUnfolding dimensions A) (actualFirstUnfolding dimensions Y) r hr hrank hY hbest

#print axioms actual_tensor_first_unfolding_best_rank_residual
end
end Reference.PaperTensorEquality
