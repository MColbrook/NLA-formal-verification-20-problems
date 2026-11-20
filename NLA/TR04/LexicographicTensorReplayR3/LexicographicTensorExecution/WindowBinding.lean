module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Concrete spectral-window execution equals the actual ordered frame predicate. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.ScanChecks
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.CyclicCombinatorics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorExecution
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexOrderedCyclicBoundary

theorem actual_equal_scan_length {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    (equalScanRun (sigmaOf A) tau).value.length=eCount A tau := by
  rw [equalScanRun_value,Reference.LexOrderedIndex.indexList_length]
  rfl

theorem actual_above_scan_length {m n : ℕ} (A : Rect m n) (tau : ℝ) :
    (aboveScanRun (sigmaOf A) tau).value.length=hCount A tau := by
  rw [aboveScanRun_value,Reference.LexOrderedIndex.indexList_length]
  rfl

theorem actual_window_mask_value {m n : ℕ} (A : Rect m n) (tau : ℝ)
    (s : ℕ) (j : Fin (eCount A tau)) (i : Fin m) :
    (windowMaskRun (sigmaOf A) tau (equalScanRun (sigmaOf A) tau).value s j.val i).value=
      decide (selected A tau s j i) := by
  rw [windowMaskRun_value,equalScanRun_value]
  congr 1
  apply propext
  unfold selected windowSelected
  by_cases he : singularValue A.transpose i.val=tau
  · simp only [sigmaOf,he,dif_pos,true_and,inWindow]
    change (tau<tau ∨ ((Reference.LexOrderedIndex.indexList (fun a : Fin m =>
        singularValue A.transpose a.val=tau)).idxOf i+
        ((Reference.LexOrderedIndex.indexList (fun a : Fin m =>
        singularValue A.transpose a.val=tau)).length-j.val))%
        (Reference.LexOrderedIndex.indexList (fun a : Fin m =>
        singularValue A.transpose a.val=tau)).length<s) ↔
      (tau<tau ∨ ((eCount A tau-j.val)+(boundaryOrdinal A tau ⟨i,he⟩).val)%(eCount A tau)<s)
    simp only [boundaryOrdinal,Reference.LexOrderedIndex.indexEnum_forward_lookup,
      Reference.LexOrderedIndex.indexList_length,eCount,EIndex,Nat.add_comm]
  · simp [sigmaOf,he]

theorem actual_window_scan_value {m n : ℕ} (A : Rect m n) (tau : ℝ)
    (s : ℕ) (j : Fin (eCount A tau)) :
    (windowScanRun (sigmaOf A) tau (equalScanRun (sigmaOf A) tau).value s j.val).value=
      Reference.LexOrderedIndex.indexList (selected A tau s j) := by
  simp only [windowScanRun,filterRun_value,actual_window_mask_value,Reference.LexOrderedIndex.indexList]

theorem actual_window_scan_charge {m n : ℕ} (A : Rect m n) (tau : ℝ)
    (s : ℕ) (j : Fin (eCount A tau)) :
    charge (windowScanRun (sigmaOf A) tau (equalScanRun (sigmaOf A) tau).value s j.val) ≤ m*(3*m+10) := by
  have h:=windowScanRun_charge (sigmaOf A) tau (equalScanRun (sigmaOf A) tau).value s j.val
  have hl : (equalScanRun (sigmaOf A) tau).value.length ≤ m := by
    rw [equalScanRun_value]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  nlinarith

#print axioms actual_equal_scan_length
#print axioms actual_above_scan_length
#print axioms actual_window_mask_value
#print axioms actual_window_scan_value
#print axioms actual_window_scan_charge
end
end Reference.LexTensorExecution
