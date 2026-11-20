module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual optimal-approximation equality projectors, extending the checked real
MI-13/RA02 adaptations at e375a6fc0a12df52c4f5a38b53df78b837e1c390.
New reference-only equality proofs by Codex, 2026-10-03. -/
public import NLA.TR04.OptimalityEquality.OptimalRows

@[expose] public section

set_option autoImplicit false
namespace Reference.RealOptimalityEquality
noncomputable section
open Reference.RealSVDPackage Reference.RealColumnCompression
open scoped BigOperators Matrix

theorem masked_projection_mul_eq_zero {m n : ℕ}
    (V : Square m) (f : Fin m → ℝ) (E : Rect m n)
    (hrow : ∀ i, f i ≠ 0 → ∀ j, (V.transpose * E) i j = 0) :
    (V * Matrix.diagonal f * V.transpose) * E = 0 := by
  have hz : Matrix.diagonal f * (V.transpose * E) = 0 := by
    ext i j
    rw [Matrix.diagonal_mul]
    by_cases hi : f i = 0
    · simp [hi]
    · simp [hrow i hi j]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hz, Matrix.mul_zero]

theorem leftAboveProjector_transpose {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    (leftAboveProjector A tau).transpose = leftAboveProjector A tau := by
  simp only [leftAboveProjector, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

theorem leftLeadingProjector_transpose {m n : ℕ} (A : Rect m n) (r : ℕ) :
    (leftLeadingProjector A r).transpose = leftLeadingProjector A r := by
  simp only [leftLeadingProjector, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.diagonal_transpose, Matrix.mul_assoc]

/-- Every best rank-r residual vanishes on actual left singular vectors strictly
above the positive boundary value, including a partial boundary tie. -/
theorem left_above_annihilates_optimal_residual {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r)
    (htau : 0 < singularValue A (r-1)) (hB : B.rank ≤ r)
    (hopt : frobeniusSq (A-B) = singularTailSq A r) :
    leftAboveProjector A (singularValue A (r-1)) * (A-B) = 0 := by
  classical
  let t := singularValue A (r-1)
  have ht : 0 < t := htau
  have hmono := (singular_values_semantics A.transpose).2.1
  have hpos := (singular_values_semantics A.transpose).1
  have hb : ∀ i : Fin m, r ≤ i.val → singularValue A.transpose i.val ^ 2 ≤ t^2 := by
    intro i hi
    have hle : singularValue A.transpose i.val ≤ t := by
      have hs := hmono (show r-1 ≤ i.val by omega)
      simpa only [singularValue_transpose, t] using hs
    nlinarith [hpos i.val]
  have ha : ∀ i : Fin m, i.val < r → t^2 ≤ singularValue A.transpose i.val ^ 2 := by
    intro i hi
    have hle : t ≤ singularValue A.transpose i.val := by
      have hs := hmono (show i.val ≤ r-1 by omega)
      simpa only [singularValue_transpose, t] using hs
    nlinarith [hpos i.val]
  have hrows := actual_optimal_residual_gram_row_zero A B r hB hopt
    (t^2) (sq_nonneg t) hb ha
  unfold leftAboveProjector
  apply masked_projection_mul_eq_zero
  intro i hi j
  have hi' : t < singularValue A.transpose i.val := by
    by_contra hh
    simp only [t, if_neg hh, ne_eq, not_true_eq_false] at hi
  have hs : t^2 < singularValue A.transpose i.val ^ 2 := by
    have hp := mul_pos (sub_pos.mpr hi') (by linarith : 0 < singularValue A.transpose i.val+t)
    nlinarith
  exact hrows i hs j

/-- If the boundary tie is completely included (the next singular value is
strictly smaller), the entire leading left projector annihilates the residual. -/
theorem left_leading_annihilates_optimal_residual {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r)
    (htau : 0 < singularValue A (r-1)) (hB : B.rank ≤ r)
    (hopt : frobeniusSq (A-B) = singularTailSq A r)
    (hgap : singularValue A r < singularValue A (r-1)) :
    leftLeadingProjector A r * (A-B) = 0 := by
  classical
  let t := singularValue A (r-1)
  let u := singularValue A r
  let c := (t^2+u^2)/2
  have ht : 0 < t := htau
  have hu : 0 ≤ u := (singular_values_semantics A).1 r
  have hug : u < t := hgap
  have hp := mul_pos (sub_pos.mpr hug) (by linarith : 0 < t+u)
  have huc : u^2 < c := by dsimp [c]; nlinarith
  have hct : c < t^2 := by dsimp [c]; nlinarith
  have hc : 0 ≤ c := by nlinarith [sq_nonneg u]
  have hmono := (singular_values_semantics A.transpose).2.1
  have hpos := (singular_values_semantics A.transpose).1
  have hb : ∀ i : Fin m, r ≤ i.val → singularValue A.transpose i.val ^ 2 ≤ c := by
    intro i hi
    have hle : singularValue A.transpose i.val ≤ u := by
      simpa only [singularValue_transpose, u] using hmono hi
    nlinarith [hpos i.val]
  have ha : ∀ i : Fin m, i.val < r → c ≤ singularValue A.transpose i.val ^ 2 := by
    intro i hi
    have hle : t ≤ singularValue A.transpose i.val := by
      have hs := hmono (show i.val ≤ r-1 by omega)
      simpa only [singularValue_transpose, t] using hs
    nlinarith [hpos i.val]
  have hrows := actual_optimal_residual_gram_row_zero A B r hB hopt c hc hb ha
  unfold leftLeadingProjector
  apply masked_projection_mul_eq_zero
  intro i hi j
  have hir : i.val < r := by
    by_contra hh
    simp [headMask, hh] at hi
  have hle : t ≤ singularValue A.transpose i.val := by
    have hs := hmono (show i.val ≤ r-1 by omega)
    simpa only [singularValue_transpose, t] using hs
  have hs : c < singularValue A.transpose i.val ^ 2 := by nlinarith [hpos i.val]
  exact hrows i hs j

theorem right_above_annihilates_optimal_residual {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r)
    (htau : 0 < singularValue A (r-1)) (hB : B.rank ≤ r)
    (hopt : frobeniusSq (A-B) = singularTailSq A r) :
    (A-B) * rightAboveProjector A (singularValue A (r-1)) = 0 := by
  have hBt : B.transpose.rank ≤ r := by simpa only [Matrix.rank_transpose] using hB
  have hoptT : frobeniusSq (A.transpose-B.transpose) = singularTailSq A.transpose r := by
    simpa only [← Matrix.transpose_sub, frobeniusSq_transpose,
      singularTailSq_transpose] using hopt
  have htauT : 0 < singularValue A.transpose (r-1) := by
    simpa only [singularValue_transpose] using htau
  have h := left_above_annihilates_optimal_residual A.transpose B.transpose r hr htauT hBt hoptT
  have hT := congrArg Matrix.transpose h
  simpa only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_transpose,
    Matrix.transpose_zero, leftAboveProjector_transpose, singularValue_transpose,
    rightAboveProjector] using hT

theorem right_leading_annihilates_optimal_residual {m n : ℕ}
    (A B : Rect m n) (r : ℕ) (hr : 0 < r)
    (htau : 0 < singularValue A (r-1)) (hB : B.rank ≤ r)
    (hopt : frobeniusSq (A-B) = singularTailSq A r)
    (hgap : singularValue A r < singularValue A (r-1)) :
    (A-B) * rightLeadingProjector A r = 0 := by
  have hBt : B.transpose.rank ≤ r := by simpa only [Matrix.rank_transpose] using hB
  have hoptT : frobeniusSq (A.transpose-B.transpose) = singularTailSq A.transpose r := by
    simpa only [← Matrix.transpose_sub, frobeniusSq_transpose,
      singularTailSq_transpose] using hopt
  have htauT : 0 < singularValue A.transpose (r-1) := by
    simpa only [singularValue_transpose] using htau
  have hgapT : singularValue A.transpose r < singularValue A.transpose (r-1) := by
    simpa only [singularValue_transpose] using hgap
  have h := left_leading_annihilates_optimal_residual A.transpose B.transpose r hr htauT hBt hoptT hgapT
  have hT := congrArg Matrix.transpose h
  simpa only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_transpose,
    Matrix.transpose_zero, leftLeadingProjector_transpose, rightLeadingProjector] using hT

#print axioms left_above_annihilates_optimal_residual
#print axioms left_leading_annihilates_optimal_residual
#print axioms right_above_annihilates_optimal_residual
#print axioms right_leading_annihilates_optimal_residual
end
end Reference.RealOptimalityEquality
