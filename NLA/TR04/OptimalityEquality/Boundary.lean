module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual matrix-rank and full-boundary-tie bridge for main.tex lem:tr04-equality.
Extends real MI-13/RA02 proofs at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.OptimalityEquality.BoundaryDefinitions
public import NLA.TR04.OptimalityEquality.Optimality

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage
open scoped Matrix

theorem singularValue_pos_iff_lt_rank {m n : ℕ} (A : Rect m n) (k : ℕ) :
    0 < singularValue A k ↔ k < A.rank := by
  have hRank : A.rank = Module.finrank ℝ (LinearMap.range (euclideanLin A)) :=
    Matrix.rank_eq_finrank_range_toLin A
      (PiLp.basisFun 2 ℝ (Fin m)) (PiLp.basisFun 2 ℝ (Fin n))
  simpa only [singularValue, hRank] using
    (euclideanLin A).singularValues_pos_iff_lt_finrank_range (n := k)

theorem positive_boundary_of_rank_gt {m n : ℕ} (A : Rect m n)
    (r : ℕ) (hrank : r < A.rank) : 0 < singularValue A (r-1) :=
  (singularValue_pos_iff_lt_rank A (r-1)).mpr (by omega)

/-- When the boundary tie is fully retained (the next singular value is smaller),
the actual above-boundary and entire boundary-eigenspace projectors sum to the
leading projector. The masks use the genuine Mathlib singular values. -/
theorem above_add_boundary_eq_leading_of_gap {m n : ℕ} (A : Rect m n)
    (r : ℕ) (hr : 0 < r)
    (hgap : singularValue A r < singularValue A (r-1)) :
    leftAboveProjector A (singularValue A (r-1)) +
      leftBoundaryProjector A (singularValue A (r-1)) = leftLeadingProjector A r := by
  classical
  let t := singularValue A (r-1)
  let a : Fin m → ℝ := fun i => if t < singularValue A.transpose i.val then 1 else 0
  let b : Fin m → ℝ := fun i => if singularValue A.transpose i.val = t then 1 else 0
  have hm := (singular_values_semantics A.transpose).2.1
  have hmask : a + b = headMask m r := by
    funext i
    by_cases hi : i.val < r
    · have hle : t ≤ singularValue A.transpose i.val := by
        simpa only [singularValue_transpose, t] using hm (show i.val ≤ r-1 by omega)
      by_cases he : singularValue A.transpose i.val = t
      · simp [a, b, headMask, hi, he]
      · have hlt : t < singularValue A.transpose i.val := lt_of_le_of_ne hle (Ne.symm he)
        simp [a, b, headMask, hi, he, hlt]
    · have hle : singularValue A.transpose i.val ≤ singularValue A r := by
        simpa only [singularValue_transpose] using hm (show r ≤ i.val by omega)
      have hlt : singularValue A.transpose i.val < t := hle.trans_lt hgap
      have he : singularValue A.transpose i.val ≠ t := ne_of_lt hlt
      simp [a, b, headMask, hi, he, not_lt_of_ge hlt.le]
  change leftVectorMatrix A * Matrix.diagonal a * (leftVectorMatrix A).transpose +
      leftVectorMatrix A * Matrix.diagonal b * (leftVectorMatrix A).transpose = _
  rw [← Matrix.add_mul, ← Matrix.mul_add, Matrix.diagonal_add]
  change leftVectorMatrix A * Matrix.diagonal (a + b) * (leftVectorMatrix A).transpose = _
  rw [hmask]
  rfl

theorem left_above_annihilates_best_rank_residual_of_rank_gt {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r) (hrank : r < A.rank) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C)) :
    leftAboveProjector A (singularValue A (r-1)) * (A-B) = 0 :=
  left_above_annihilates_actual_best_rank_residual A B r hr
    (positive_boundary_of_rank_gt A r hrank) hB hbest

theorem left_full_boundary_annihilates_best_rank_residual_of_rank_gt {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r) (hrank : r < A.rank) (hB : B.rank ≤ r)
    (hbest : ∀ C : Rect m n, C.rank ≤ r → frobeniusSq (A-B) ≤ frobeniusSq (A-C))
    (hgap : singularValue A r < singularValue A (r-1)) :
    (leftAboveProjector A (singularValue A (r-1)) +
      leftBoundaryProjector A (singularValue A (r-1))) * (A-B) = 0 := by
  rw [above_add_boundary_eq_leading_of_gap A r hr hgap]
  exact left_leading_annihilates_actual_best_rank_residual A B r hr
    (positive_boundary_of_rank_gt A r hrank) hB hbest hgap

#print axioms singularValue_pos_iff_lt_rank
#print axioms above_add_boundary_eq_leading_of_gap
#print axioms left_above_annihilates_best_rank_residual_of_rank_gt
#print axioms left_full_boundary_annihilates_best_rank_residual_of_rank_gt
end
end Reference.RealOptimalityEquality
