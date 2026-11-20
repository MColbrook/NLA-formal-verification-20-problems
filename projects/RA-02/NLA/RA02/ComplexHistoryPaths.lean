module

public import NLA.RA02.ComplexHistoryAlgebra
public import NLA.RA02.PathSemantics

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.RA02.Paper.ComplexHistory

theorem cholesky_step_cross {n : ℕ} (A : NLA.RA02.Square n) (j : Fin n) :
    NLA.RA02.choleskyStep A j = crossUpdate A j j := by
  by_cases hj : A j j = 0 <;> ext a b <;> simp [NLA.RA02.choleskyStep,crossUpdate,hj]

theorem lu_step_cross {n : ℕ} (A : NLA.RA02.Square n) (i j : Fin n) :
    NLA.RA03.nextResidual A (some (i,j)) = crossUpdate A i j := by
  by_cases hj : A i j = 0 <;> ext a b <;> simp [NLA.RA03.nextResidual,NLA.RA03.pivotResidual,crossUpdate,hj]

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

theorem residual_empty (n : ℕ) (A : NLA.RA02.Square n) (rows cols : Fin 0 ↪ Fin n) :
    interpolatoryResidual A rows cols = A := by
  ext i j
  simp [interpolatoryResidual, Matrix.mul_apply]

theorem choleskyPath_distinct {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (h : Fin k ↪ Fin n) :
    NLA.RA02.pathResidual A (List.ofFn h) = interpolatoryResidual A h h := by
  induction k with
  | zero => simp [List.ofFn_zero, NLA.RA02.pathResidual, residual_empty]
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
    rw [List.ofFn_succ', List.concat_eq_append, NLA.RA02.pathResidual_append]
    change NLA.RA02.choleskyStep (NLA.RA02.pathResidual A (List.ofFn g)) (h (Fin.last k)) = _
    rw [cholesky_step_cross, ih hg g, residual_append_update A g g _ _ (history_last_not_in_prefix h)
      (history_last_not_in_prefix h) hu haq]
    simpa only [g, happ]

def luListPath {n : ℕ} : NLA.RA02.Square n → List (NLA.RA03.Pivot n n) → NLA.RA02.Square n
  | A, [] => A
  | A, p :: w => luListPath (NLA.RA03.nextResidual A p) w

theorem luPath_as_list {n k : ℕ} (A : NLA.RA02.Square n)
    (h : Fin k → NLA.RA03.Pivot n n) :
    NLA.RA03.historyResidual A h = luListPath A (List.ofFn h) := by
  induction k generalizing A with
  | zero => rfl
  | succ k ih => rw [NLA.RA03.historyResidual, List.ofFn_succ, luListPath, ih]

theorem luListPath_append {n : ℕ} (A : NLA.RA02.Square n) (u w : List (NLA.RA03.Pivot n n)) :
    luListPath A (u++w) = luListPath (luListPath A u) w := by
  induction u generalizing A with
  | nil => rfl
  | cons p u ih => simpa only [List.cons_append, luListPath] using ih (NLA.RA03.nextResidual A p)

theorem luListPath_distinct {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (rows cols : Fin k ↪ Fin n) :
    luListPath A (List.ofFn (fun i => some (rows i,cols i))) = interpolatoryResidual A rows cols := by
  induction k with
  | zero => simp [List.ofFn_zero, luListPath, residual_empty]
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
    rw [List.ofFn_succ', List.concat_eq_append, luListPath_append]
    change NLA.RA03.nextResidual (luListPath A (List.ofFn (fun i => some (gr i,gc i))))
      (some (rows (Fin.last k),cols (Fin.last k))) = _
    rw [lu_step_cross, ih hg gr gc, residual_append_update A gr gc _ _ (history_last_not_in_prefix rows)
      (history_last_not_in_prefix cols) hu haq]
    simpa only [gr, gc, hr, hc]

theorem luPath_distinct {n k : ℕ} (A : NLA.RA02.Square n)
    (hA : AllSquareMinorsNonzero A) (hk : k ≤ n) (rows cols : Fin k ↪ Fin n) :
    NLA.RA03.historyResidual A (fun i => some (rows i,cols i)) = interpolatoryResidual A rows cols := by
  rw [luPath_as_list, luListPath_distinct A hA hk rows cols]

#print axioms luPath_distinct
end NLA.RA02.Paper.ComplexHistory
