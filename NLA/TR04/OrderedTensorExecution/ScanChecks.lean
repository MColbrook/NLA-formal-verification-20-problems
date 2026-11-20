module

/- Exact scan and index-window semantics and uniform derived charges. -/
public import NLA.TR04.OrderedTensorExecution.ScanDefinitions
public import NLA.TR04.OrderedTensorExecution.FiniteScans
public import NLA.TR04.OrderedTensorSolver.IndexChecks
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage

@[simp] theorem readRun_value (x : ℝ) : (readRun x).value=x := rfl
@[simp] theorem readRun_charge (x : ℝ) : charge (readRun x)=1 := rfl
@[simp] theorem lessRealRun_value (x y : ℝ) : (lessRealRun x y).value=decide (x<y) := rfl
@[simp] theorem lessRealRun_charge (x y : ℝ) : charge (lessRealRun x y)=1 := rfl

theorem equalScanRun_value {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ) :
    (equalScanRun sigma tau).value=Reference.OrderedIndex.indexList (fun i => sigma i=tau) := by
  simp [equalScanRun,Reference.OrderedIndex.indexList]

theorem aboveScanRun_value {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ) :
    (aboveScanRun sigma tau).value=Reference.OrderedIndex.indexList (fun i => tau<sigma i) := by
  simp [aboveScanRun,Reference.OrderedIndex.indexList]

theorem equalScanRun_charge {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ) :
    charge (equalScanRun sigma tau) ≤ 3*m := by
  simpa [equalScanRun,Nat.mul_comm] using
    filterRun_charge (fun i => bindRun (readRun (sigma i)) fun x => equalRealRun x tau)
      (List.finRange m) 2 (by intro i hi; simp)

theorem aboveScanRun_charge {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ) :
    charge (aboveScanRun sigma tau) ≤ 3*m := by
  simpa [aboveScanRun,Nat.mul_comm] using
    filterRun_charge (fun i => bindRun (readRun (sigma i)) fun x => lessRealRun tau x)
      (List.finRange m) 2 (by intro i hi; simp)

theorem windowMaskRun_value {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ) (i : Fin m) :
    (windowMaskRun sigma tau boundary s j i).value=
      decide (tau<sigma i ∨ sigma i=tau ∧ (boundary.idxOf i+(boundary.length-j))%boundary.length<s) := by
  by_cases ha : tau<sigma i
  · simp [windowMaskRun,ha]
  · by_cases he : sigma i=tau
    · simp [windowMaskRun,he]
    · simp [windowMaskRun,ha,he]

theorem windowMaskRun_charge {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ) (i : Fin m) :
    charge (windowMaskRun sigma tau boundary s j i) ≤ 3*boundary.length+9 := by
  have h := ordinalRun_charge i boundary
  by_cases ha : tau<sigma i
  · simp [windowMaskRun,ha]
  · by_cases he : sigma i=tau
    · simp [windowMaskRun,he]; omega
    · simp [windowMaskRun,ha,he]

theorem windowScanRun_charge {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ) :
    charge (windowScanRun sigma tau boundary s j) ≤ m*(3*boundary.length+10) := by
  simpa [windowScanRun] using
    filterRun_charge (windowMaskRun sigma tau boundary s j) (List.finRange m)
      (3*boundary.length+9) (by intro i hi; exact windowMaskRun_charge sigma tau boundary s j i)

#print axioms equalScanRun_value
#print axioms aboveScanRun_value
#print axioms equalScanRun_charge
#print axioms aboveScanRun_charge
#print axioms windowMaskRun_value
#print axioms windowMaskRun_charge
#print axioms windowScanRun_charge
end
end Reference.OrderedTensorExecution
