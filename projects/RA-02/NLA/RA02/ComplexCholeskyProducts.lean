module

public import NLA.RA02.ComplexHistoryTerminal
public import NLA.RA02.HistoryProducts

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper.ComplexHistory

theorem diagonal_cast_real {n : ℕ} (A : NLA.RA02.Square n) (hA : A.PosSemidef) (j : Fin n) :
    ((A j j).re : ℂ) = A j j := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (hA.diag_nonneg (i := j))).2

theorem trace_cast_real {n : ℕ} (A : NLA.RA02.Square n) (hA : A.PosSemidef) :
    (NLA.RA02.realTrace A : ℂ) = A.trace := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp hA.trace_nonneg).2

theorem cholesky_pivotProduct_det {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hpsd : A.PosSemidef) (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    (NLA.RA02.pivotProduct A (List.ofFn h) : ℂ) = (A.submatrix h h).det := by
  induction k with
  | zero => simp [List.ofFn_zero, Matrix.det_isEmpty]
  | succ k ih =>
    let g := historyPrefix h (Nat.le_succ k)
    have hg : k ≤ n := by omega
    have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k hg g g))
    rw [List.ofFn_succ', List.concat_eq_append, NLA.RA02.pivotProduct_append_singleton, Complex.ofReal_mul]
    change (NLA.RA02.pivotProduct A (List.ofFn g) : ℂ) *
      (((NLA.RA02.pathResidual A (List.ofFn g)) (h (Fin.last k)) (h (Fin.last k))).re : ℂ) = _
    rw [ih hg g, diagonal_cast_real _ (NLA.RA02.pathResidual_posSemidef A hpsd _) _,
      choleskyPath_distinct A hA hg g]
    rw [← residual_bordered_determinant A g g _ _ (history_last_not_in_prefix h)
      (history_last_not_in_prefix h) hu]
    simpa only [g, history_append_prefix]

theorem cholesky_pathWeight_det {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hpsd : A.PosSemidef) (hk : k ≤ n) (h : Fin k ↪ Fin n)
    (htrace : ∀ s : Fin (List.ofFn h).length,
      NLA.RA02.realTrace (NLA.RA02.pathResidual A ((List.ofFn h).take s.val)) ≠ 0) :
    (NLA.RA02.pathWeight A (List.ofFn h) : ℂ) =
      (A.submatrix h h).det / (NLA.RA02.prefixTraceProduct A (List.ofFn h) : ℂ) := by
  rw [NLA.RA02.pathWeight_eq_pivotProduct_div _ _ htrace, Complex.ofReal_div,
    cholesky_pivotProduct_det A hA hpsd hk h]

end NLA.RA02.Paper.ComplexHistory
