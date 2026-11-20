module

public import NLA.TR04.AllOrderSharp.Tag

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix

namespace NLA.TR04.AllOrderSharp
open Reference.LexTensorCompletion
set_option maxRecDepth 4096

@[simp] theorem branchWord_zero {N : ℕ} (hN : 0 < N) (q : ℕ) :
    branchWord N hN q ⟨0, hN⟩ = zeroWord N hN (q+1) := by
  induction q with
  | zero => rfl
  | succ q ih => simp [branchWord, zeroWord, ih] <;> rfl

theorem activeWord_castSucc {N q : ℕ} (hN : q+3 ≤ N) (b : Fin (q+2)) :
    activeWord hN b.castSucc =
      (⟨b.val, b.isLt.trans_le (show q+2 ≤ N by omega)⟩,
        activeWord (show q+2 ≤ N by omega) b) := by
  simp [activeWord, branchWord, b.isLt] <;> rfl

theorem activeWord_last {N q : ℕ} (hN : q+3 ≤ N) :
    activeWord hN (Fin.last (q+2)) =
      (⟨q+2, by omega⟩, zeroWord N (by omega) (q+1)) := by
  simp [activeWord, branchWord] <;> rfl

theorem activeWord_zero {N q : ℕ} (hN : q+2 ≤ N) :
    activeWord hN (0 : Fin (q+2)) = zeroWord N (by omega) (q+1) := by
  simpa [activeWord] using branchWord_zero (show 0 < N by omega) q

theorem merge_family_apply {N q m : ℕ} (hN : q+3 ≤ N)
    (V : Matrix (Fin m) (Fin (q+3)) ℝ)
    (i : Fin (rowCount m N)) (j : ModeIndex (List.replicate (q+1) N)) :
    merge (family hN V) i j = ∑ b,
      @ite ℝ ((((rowEquiv m N).symm i).2, j) = activeWord hN b)
        (Reference.RecursiveTensorCompletion.modeIndexDecidableEq
          (List.replicate (q+1+1) N) _ _)
        (V ((rowEquiv m N).symm i).1 b) 0 := by
  exact family_apply hN V ((rowEquiv m N).symm i).1
    (((rowEquiv m N).symm i).2, j)

def collapseColumns {N q m : ℕ} (hN : q+3 ≤ N)
    (V : Matrix (Fin m) (Fin (q+3)) ℝ) :
    Matrix (Fin (rowCount m N)) (Fin (q+2)) ℝ :=
  tag (show q+2 ≤ N by omega) (fun i b => V i b.castSucc) +
    Matrix.of (fun (i : Fin (rowCount m N)) (b : Fin (q+2)) =>
      if b.val = 0 ∧ ((rowEquiv m N).symm i).2.val = q+2
      then V ((rowEquiv m N).symm i).1 (Fin.last (q+2)) else 0)

theorem family_add {N q m : ℕ} (hN : q+2 ≤ N)
    (V W : Matrix (Fin m) (Fin (q+2)) ℝ) :
    family hN (V+W) = family hN V + family hN W := by
  exact Matrix.add_mul V W (selector hN)

theorem merge_family {N q m : ℕ} (hN : q+3 ≤ N)
    (V : Matrix (Fin m) (Fin (q+3)) ℝ) :
    merge (family hN V) = family (show q+2 ≤ N by omega) (collapseColumns hN V) := by
  unfold collapseColumns
  rw [family_add]
  ext i j
  simp only [Matrix.add_apply, merge_family_apply, family_apply]
  rw [Fin.sum_univ_castSucc]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro b _
    rw [activeWord_castSucc]
    by_cases hfirst : ((rowEquiv m N).symm i).2.val = b.val
    · by_cases hword : j = activeWord (show q+2 ≤ N by omega) b
      · simp [tag, Fin.ext_iff, hfirst, hword]
      · simp [tag, Fin.ext_iff, hfirst, hword]
    · simp [tag, Fin.ext_iff, hfirst]
  · symm
    rw [Finset.sum_eq_single (0 : Fin (q+2))]
    · rw [activeWord_zero, activeWord_last]
      by_cases hfirst : ((rowEquiv m N).symm i).2.val = q+2
      · by_cases hword : j = zeroWord N (show 0 < N by omega) (q+1)
        · simp only [Matrix.of_apply, Fin.val_zero, true_and, Prod.mk.injEq, Fin.ext_iff, hfirst, hword, and_true, and_false, if_true, if_false]
        · simp [Fin.ext_iff, hfirst, hword]
      · simp only [Matrix.of_apply, Fin.val_zero, true_and, Prod.mk.injEq, Fin.ext_iff, hfirst, false_and, and_false, if_false, ite_self]
    · intro b _ hb
      have hb0 : b.val ≠ 0 := by
        intro hh
        apply hb
        exact Fin.ext hh
      simp [hb]
    · simp

theorem merge_family_last_zero {N q m : ℕ} (hN : q+3 ≤ N)
    (V : Matrix (Fin m) (Fin (q+3)) ℝ)
    (hlast : ∀ i, V i (Fin.last (q+2)) = 0) :
    merge (family hN V) =
      family (show q+2 ≤ N by omega)
        (tag (show q+2 ≤ N by omega) (fun i b => V i b.castSucc)) := by
  rw [merge_family]
  congr 1
  ext i b
  simp [collapseColumns, hlast]

theorem collapseColumns_nuisance_zero {N q m : ℕ} (hN : q+3 ≤ N)
    (V : Matrix (Fin m) (Fin (q+3)) ℝ)
    (hV : ∀ i, V i ⟨1, by omega⟩ = 0) :
    ∀ i, collapseColumns hN V i ⟨1, by omega⟩ = 0 := by
  intro i
  simp only [collapseColumns, Matrix.add_apply, Matrix.of_apply, tag, Fin.val_mk, Fin.coe_castSucc]
  simp only [one_ne_zero, false_and, if_false, add_zero]
  split_ifs
  · exact hV _
  · rfl

theorem family_nuisance_zero_feasible {N q m : ℕ} (hN : q+2 ≤ N)
    (V : Matrix (Fin m) (Fin (q+2)) ℝ)
    (hV : ∀ i, V i ⟨1, by omega⟩ = 0) :
    feasible m (List.replicate (q+1) N) (family hN V) (ranks q) := by
  induction q generalizing m with
  | zero =>
    simp only [List.replicate_succ, List.replicate_zero, ranks, feasible]
    exact ⟨family_rank_column_zero hN V ⟨1, by omega⟩ hV, trivial⟩
  | succ q ih =>
    simp only [List.replicate_succ, ranks, feasible]
    constructor
    · exact family_rank_column_zero hN V ⟨1, by omega⟩ hV
    · rw [merge_family]
      exact ih (show q+2 ≤ N by omega) (collapseColumns hN V)
        (collapseColumns_nuisance_zero hN V hV)

end NLA.TR04.AllOrderSharp
