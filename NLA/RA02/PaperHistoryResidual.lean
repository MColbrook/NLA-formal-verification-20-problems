module

public import NLA.RA02.PaperHistoryDefinitions
public import NLA.RA02.PaperCholeskyBridge

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper

theorem history_last_not_in_prefix {n k : ℕ} (h : Fin (k+1) ↪ Fin n) :
    h (Fin.last k) ∉ Set.range (historyPrefix h (Nat.le_succ k)) := by
  rintro ⟨i,hi⟩
  have hh := congrArg (fun x : Fin (k+1) => x.val) (h.injective hi)
  change i.val = k at hh
  omega

theorem history_append_prefix {n k : ℕ} (h : Fin (k+1) ↪ Fin n) :
    appendEmbedding (historyPrefix h (Nat.le_succ k)) (h (Fin.last k)) (history_last_not_in_prefix h) = h := by
  ext i
  induction i using Fin.lastCases with
  | last => simp [appendEmbedding]
  | cast i =>
    simp only [appendEmbedding, Function.Embedding.coeFn_mk, Fin.snoc_castSucc, historyPrefix]
    rfl

theorem residual_empty (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (rows cols : Fin 0 ↪ Fin n) :
    interpolatoryResidual A rows cols = A := by
  ext i j
  simp [interpolatoryResidual, Matrix.mul_apply]

theorem realCholeskyPath_append {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u w : List (Fin n)) :
    realCholeskyPath A (u++w) = realCholeskyPath (realCholeskyPath A u) w := by
  induction u generalizing A with
  | nil => rfl
  | cons j u ih => simpa only [List.cons_append, realCholeskyPath] using ih (crossUpdate A j j)

theorem realCholeskyPath_distinct {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    realCholeskyPath A (List.ofFn h) = interpolatoryResidual A h h := by
  induction k with
  | zero => simp [List.ofFn_zero, realCholeskyPath, residual_empty]
  | succ k ih =>
    let g := historyPrefix h (Nat.le_succ k)
    have hg : k ≤ n := by omega
    have hu := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA k hg g g))
    have ha := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (hA (k+1) hk h h))
    have happ := history_append_prefix h
    have haq : IsUnit (A.submatrix
        (appendEmbedding g (h (Fin.last k)) (history_last_not_in_prefix h))
        (appendEmbedding g (h (Fin.last k)) (history_last_not_in_prefix h))) := by
      simpa only [g, happ] using ha
    rw [List.ofFn_succ', List.concat_eq_append, realCholeskyPath_append]
    change crossUpdate (realCholeskyPath A (List.ofFn g)) (h (Fin.last k)) (h (Fin.last k)) = _
    rw [ih hg g, residual_append_update A g g _ _ (history_last_not_in_prefix h)
      (history_last_not_in_prefix h) hu haq]
    simpa only [g, happ]

theorem choleskyPath_distinct {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    NLA.RA02.pathResidual (complexify A) (List.ofFn h) =
      complexify (interpolatoryResidual A h h) := by
  rw [complexify_cholesky_path, realCholeskyPath_distinct A hA hk h]

#print axioms choleskyPath_distinct
end NLA.RA02.Paper
