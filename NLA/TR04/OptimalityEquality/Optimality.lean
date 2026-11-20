module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual arbitrary optimal real-matrix residual corollaries, extending the checked
MI-13/RA02 proofs at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.OptimalityEquality.Projectors

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage

/-- The optimal-error identity follows from actual optimality against every real
matrix of rank at most r; no numerical value of the optimum is assumed. -/
theorem actual_best_rank_error_eq_tail {m n : ℕ} (A B : Rect m n)
    (r : ℕ) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C)) :
    frobeniusSq (A-B) = singularTailSq A r := by
  obtain ⟨C, hC, he⟩ := real_rank_r_frobenius_attainment A r
  exact le_antisymm (by simpa only [he] using hbest C hC)
    (singularTail_le_lowRankError A B r hB)

theorem left_above_annihilates_actual_best_rank_residual {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r)
    (htau : 0 < singularValue A (r-1)) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C)) :
    leftAboveProjector A (singularValue A (r-1)) * (A-B) = 0 :=
  left_above_annihilates_optimal_residual A B r hr htau hB
    (actual_best_rank_error_eq_tail A B r hB hbest)

theorem left_leading_annihilates_actual_best_rank_residual {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r)
    (htau : 0 < singularValue A (r-1)) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C))
    (hgap : singularValue A r < singularValue A (r-1)) :
    leftLeadingProjector A r * (A-B) = 0 :=
  left_leading_annihilates_optimal_residual A B r hr htau hB
    (actual_best_rank_error_eq_tail A B r hB hbest) hgap

theorem right_above_annihilates_actual_best_rank_residual {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r)
    (htau : 0 < singularValue A (r-1)) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C)) :
    (A-B) * rightAboveProjector A (singularValue A (r-1)) = 0 :=
  right_above_annihilates_optimal_residual A B r hr htau hB
    (actual_best_rank_error_eq_tail A B r hB hbest)

theorem right_leading_annihilates_actual_best_rank_residual {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r)
    (htau : 0 < singularValue A (r-1)) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C))
    (hgap : singularValue A r < singularValue A (r-1)) :
    (A-B) * rightLeadingProjector A r = 0 :=
  right_leading_annihilates_optimal_residual A B r hr htau hB
    (actual_best_rank_error_eq_tail A B r hB hbest) hgap

#print axioms actual_best_rank_error_eq_tail
#print axioms left_above_annihilates_actual_best_rank_residual
#print axioms left_leading_annihilates_actual_best_rank_residual
#print axioms right_above_annihilates_actual_best_rank_residual
#print axioms right_leading_annihilates_actual_best_rank_residual
end
end Reference.RealOptimalityEquality
