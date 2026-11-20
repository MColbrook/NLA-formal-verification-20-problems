module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Fresh ascending-index implementation variant; prior frozen sources unchanged. -/
/- Genuine finite cyclic-window counts; actual H/E multiplicity bindings. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.CyclicDefinitions
public import NLA.TR04.OptimalityEquality.CountIdentity

@[expose] public section

set_option autoImplicit false
namespace Reference.LexOrderedCyclicBoundary
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped BigOperators

theorem prefix_card {t s : ℕ} (hs : s ≤ t) :
    (Finset.univ.filter (fun i : Fin t => i.val<s)).card=s := by
  classical
  calc
    _ = (Finset.univ : Finset (Fin s)).card := by
      refine Finset.card_bij (fun (i : Fin t) (hi : i ∈ Finset.univ.filter (fun i : Fin t => i.val<s)) =>
        (⟨i.val,(Finset.mem_filter.mp hi).2⟩ : Fin s)) ?_ ?_ ?_
      · intro i hi;exact Finset.mem_univ _
      · intro i hi j hj he;exact Fin.ext (congrArg (fun x : Fin s => x.val) he)
      · intro i hi
        let j : Fin t := ⟨i.val,i.isLt.trans_le hs⟩
        exact ⟨j,by simp [j,i.isLt],Fin.ext rfl⟩
    _ = s := by simp

theorem prefix_indicator_sum {t s : ℕ} (hs : s ≤ t) :
    (∑ i : Fin t, if i.val<s then (1 : ℝ) else 0)=(s : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  simp [prefix_card hs]

theorem cyclic_window_column_sum {t s : ℕ} [NeZero t] (hs : s ≤ t) (i : Fin t) :
    (∑ j : Fin t, if inWindow s j i then (1 : ℝ) else 0)=(s : ℝ) := by
  calc
    _ = ∑ j : Fin t, if j.val<s then (1 : ℝ) else 0 :=
      by
      rw [← (reflected i).sum_comp (fun j => if j.val<s then (1 : ℝ) else 0)]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : (i-j).val<s <;> simp [reflected,inWindow,h]
    _ = _ := prefix_indicator_sum hs

theorem cyclic_window_row_sum {t s : ℕ} [NeZero t] (hs : s ≤ t) (j : Fin t) :
    (∑ i : Fin t, if inWindow s j i then (1 : ℝ) else 0)=(s : ℝ) := by
  calc
    _ = ∑ i : Fin t, if i.val<s then (1 : ℝ) else 0 :=
      by
      rw [← (shifted j).sum_comp (fun i => if i.val<s then (1 : ℝ) else 0)]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : (i-j).val<s <;> simp [shifted,inWindow,h]
    _ = _ := prefix_indicator_sum hs

theorem eCount_eq_boundaryMultiplicity {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    eCount A tau=boundaryMultiplicity A tau := by
  classical
  exact Fintype.card_subtype (fun i : Fin m => singularValue A.transpose i.val=tau)
theorem hCount_eq_aboveMultiplicity {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    hCount A tau=aboveMultiplicity A tau := by
  classical
  exact Fintype.card_subtype (fun i : Fin m => tau<singularValue A.transpose i.val)

theorem actual_window_column_sum {m n : ℕ} (A : Rect m n) (tau : ℝ)
    [NeZero (eCount A tau)] (s : ℕ) (hs : s ≤ eCount A tau) (i : Fin m) :
    (∑ j : Fin (eCount A tau), indicator (windowSelected A tau s j) i)=
      (s : ℝ)*(if singularValue A.transpose i.val=tau then (1 : ℝ) else 0) := by
  classical
  by_cases he : singularValue A.transpose i.val=tau
  · simp only [indicator,windowSelected,dif_pos he,if_pos he,mul_one]
    exact cyclic_window_column_sum hs (boundaryOrdinal A tau ⟨i,he⟩)
  · simp [indicator,windowSelected,he]

#print axioms cyclic_window_column_sum
#print axioms cyclic_window_row_sum
#print axioms actual_window_column_sum
end
end Reference.LexOrderedCyclicBoundary