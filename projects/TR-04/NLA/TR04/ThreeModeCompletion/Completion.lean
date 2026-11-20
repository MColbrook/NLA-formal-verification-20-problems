module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Exact THREE-mode completion base case of main.tex lem:tr04-completion.
The actual second unfolding is approximated using proved real best-rank attainment.
No tensor, rank, error or SVD-correctness oracle is assumed.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.ThreeModeCompletion.Definitions
public import NLA.TR04.ThreeModeCompletion.FiniteMatrix

@[expose] public section

set_option autoImplicit false
namespace Reference.ThreeModeCompletion
noncomputable section
open Reference.RealSVDPackage Reference.RealColumnCompression Reference.TensorGrouping
open scoped BigOperators Matrix

theorem three_mode_completion {m n p k : ℕ}
    (A : ThreeTensor m n p) (U : Rect m k) (hU : U.transpose * U = 1)
    (r1 r2 : ℕ) (hk : k ≤ r1) :
    ∃ X : ThreeTensor m n p, feasibleThree X r1 r2 ∧
      ∀ Y : ThreeTensor m n p, feasibleThree Y r1 r2 →
        tensorFrobeniusSq (A-X) ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
          tensorFrobeniusSq (U.transpose*(A-Y)) ∧
        tensorFrobeniusSq (A-X) ≤ tensorFrobeniusSq (A-U*U.transpose*A) +
          tensorFrobeniusSq (U*U.transpose*(A-Y)) := by
  classical
  obtain ⟨B, hB, hmin⟩ := finite_best_rank_frobenius_attainment (grouped (U.transpose*A)) r2
  let C : ThreeTensor k n p := fun i j => B (i,j.1) j.2
  have hgroup : grouped C = B := rfl
  let X := U*C
  have hfirst : X.rank ≤ r1 :=
    (Matrix.rank_mul_le_left U C).trans ((Matrix.rank_le_width U).trans hk)
  have hsecond : (secondUnfolding X).rank ≤ r2 := by
    change (grouped (U*C)).rank ≤ r2
    have h := grouped_lifting_rank_le U C
    rw [hgroup] at h
    exact h.trans hB
  refine ⟨X, ⟨hfirst,hsecond⟩, ?_⟩
  intro Y hY
  have hYrank : (grouped (U.transpose*Y)).rank ≤ r2 :=
    (grouped_compression_rank_le U Y).trans hY.2
  have happrox : entryFrobeniusSq (U.transpose*A-C) ≤
      entryFrobeniusSq (U.transpose*(A-Y)) := by
    rw [← grouped_frobeniusSq (U.transpose*A-C),
      ← grouped_frobeniusSq (U.transpose*(A-Y))]
    have ha : grouped (U.transpose*A-C) = grouped (U.transpose*A)-B := rfl
    have hb : grouped (U.transpose*(A-Y)) = grouped (U.transpose*A)-grouped (U.transpose*Y) := by
      rw [Matrix.mul_sub]
      rfl
    rw [ha,hb]
    exact hmin _ hYrank
  have hd := finite_orthonormal_column_error_decomposition U hU A C
  have hbound : entryFrobeniusSq (A-X) ≤ entryFrobeniusSq (A-U*U.transpose*A) +
      entryFrobeniusSq (U.transpose*(A-Y)) := by
    change entryFrobeniusSq (A-U*C) ≤ _
    rw [hd]
    exact add_le_add le_rfl happrox
  have hnorm := finite_column_lifting_frobenius_eq U hU (U.transpose*(A-Y))
  have hnorm' : entryFrobeniusSq (U*U.transpose*(A-Y)) =
      entryFrobeniusSq (U.transpose*(A-Y)) := by
    simpa only [Matrix.mul_assoc] using hnorm
  change entryFrobeniusSq (A-X) ≤ entryFrobeniusSq (A-U*U.transpose*A) +
    entryFrobeniusSq (U.transpose*(A-Y)) ∧
    entryFrobeniusSq (A-X) ≤ entryFrobeniusSq (A-U*U.transpose*A) +
    entryFrobeniusSq (U*U.transpose*(A-Y))
  exact ⟨hbound, by rw [hnorm']; exact hbound⟩

#print axioms three_mode_completion
end
end Reference.ThreeModeCompletion
