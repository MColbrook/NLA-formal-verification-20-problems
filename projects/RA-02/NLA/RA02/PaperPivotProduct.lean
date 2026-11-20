module

public import NLA.RA02.PaperHistoryResidual
public import NLA.RA02.HistoryProducts

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

/-- The product of the actual chronological Cholesky pivots telescopes to
the selected principal determinant, for every distinct history. -/
theorem cholesky_pivotProduct_det {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    NLA.RA02.pivotProduct (complexify A) (List.ofFn h) = (A.submatrix h h).det := by
  induction k with
  | zero => simp [List.ofFn_zero, Matrix.det_isEmpty]
  | succ k ih =>
    let g := historyPrefix h (Nat.le_succ k)
    have hg : k ≤ n := by omega
    have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k hg g g))
    rw [List.ofFn_succ', List.concat_eq_append, NLA.RA02.pivotProduct_append_singleton]
    change NLA.RA02.pivotProduct (complexify A) (List.ofFn g) *
      ((NLA.RA02.pathResidual (complexify A) (List.ofFn g)) (h (Fin.last k)) (h (Fin.last k))).re = _
    rw [ih hg g, choleskyPath_distinct A hA hg g]
    change (A.submatrix g g).det * interpolatoryResidual A g g (h (Fin.last k)) (h (Fin.last k)) = _
    rw [← residual_bordered_determinant A g g _ _ (history_last_not_in_prefix h)
      (history_last_not_in_prefix h) hu]
    simpa only [g, history_append_prefix]

theorem cholesky_pathWeight_det {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (h : Fin k ↪ Fin n)
    (htrace : ∀ s : Fin (List.ofFn h).length,
      NLA.RA02.realTrace (NLA.RA02.pathResidual (complexify A) ((List.ofFn h).take s.val)) ≠ 0) :
    NLA.RA02.pathWeight (complexify A) (List.ofFn h) =
      (A.submatrix h h).det / NLA.RA02.prefixTraceProduct (complexify A) (List.ofFn h) := by
  rw [NLA.RA02.pathWeight_eq_pivotProduct_div _ _ htrace, cholesky_pivotProduct_det A hA hk h]

#print axioms cholesky_pathWeight_det
end NLA.RA02.Paper
