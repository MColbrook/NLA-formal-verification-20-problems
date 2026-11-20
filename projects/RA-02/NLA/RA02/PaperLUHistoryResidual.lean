module

public import NLA.RA02.PaperHistoryResidual
public import NLA.RA02.PaperLUBridge

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem realLUPath_as_list {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : Fin k → Option (Fin n × Fin n)) : realLUPath A h = realLUListPath A (List.ofFn h) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih =>
    rw [realLUPath, List.ofFn_succ, realLUListPath, ih]

theorem realLUListPath_append {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (u w : List (Option (Fin n × Fin n))) :
    realLUListPath A (u++w) = realLUListPath (realLUListPath A u) w := by
  induction u generalizing A with
  | nil => rfl
  | cons p u ih => simpa only [List.cons_append, realLUListPath] using ih (realLUNext A p)

theorem realLUPath_distinct {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (rows cols : Fin k ↪ Fin n) :
    realLUListPath A (List.ofFn (fun i => some (rows i,cols i))) = interpolatoryResidual A rows cols := by
  induction k with
  | zero => simp [List.ofFn_zero, realLUListPath, residual_empty]
  | succ k ih =>
    let gr := historyPrefix rows (Nat.le_succ k)
    let gc := historyPrefix cols (Nat.le_succ k)
    have hg : k ≤ n := by omega
    have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k hg gr gc))
    have ha := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA (k+1) hk rows cols))
    have hr := history_append_prefix rows
    have hc := history_append_prefix cols
    have haq : IsUnit (A.submatrix
        (appendEmbedding gr (rows (Fin.last k)) (history_last_not_in_prefix rows))
        (appendEmbedding gc (cols (Fin.last k)) (history_last_not_in_prefix cols))) := by
      simpa only [gr, gc, hr, hc] using ha
    rw [List.ofFn_succ', List.concat_eq_append, realLUListPath_append]
    change crossUpdate (realLUListPath A (List.ofFn (fun i => some (gr i,gc i))))
      (rows (Fin.last k)) (cols (Fin.last k)) = _
    rw [ih hg gr gc, residual_append_update A gr gc _ _ (history_last_not_in_prefix rows)
      (history_last_not_in_prefix cols) hu haq]
    simpa only [gr, gc, hr, hc]

theorem luPath_distinct {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (rows cols : Fin k ↪ Fin n) :
    NLA.RA03.historyResidual (complexify A) (fun i => some (rows i,cols i)) =
      complexify (interpolatoryResidual A rows cols) := by
  rw [complexify_lu_path, realLUPath_as_list, realLUPath_distinct A hA hk rows cols]

#print axioms luPath_distinct
end NLA.RA02.Paper
