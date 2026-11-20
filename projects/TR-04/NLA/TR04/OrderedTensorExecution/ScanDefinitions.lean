module

/- Literal finite original-index scans and cyclic-window mask execution. -/
public import NLA.TR04.OrderedTensorExecution.Definitions
public import NLA.TR04.TensorArithmeticExecution.DenseLoops

@[expose] public section

set_option autoImplicit false
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage

def readRun (x : ℝ) : Run ℝ := liftRun (Reference.TensorArithmeticExecution.readReal x)
def lessRealRun (x y : ℝ) : Run Bool := liftRun (Reference.TensorArithmeticExecution.lessReal x y)

def equalScanRun {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ) : Run (List (Fin m)) :=
  filterRun (fun i => bindRun (readRun (sigma i)) fun x => equalRealRun x tau) (List.finRange m)

def aboveScanRun {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ) : Run (List (Fin m)) :=
  filterRun (fun i => bindRun (readRun (sigma i)) fun x => lessRealRun tau x) (List.finRange m)

def windowMaskRun {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ) (i : Fin m) : Run Bool :=
  bindRun (readRun (sigma i)) fun x =>
  bindRun (lessRealRun tau x) fun above =>
  bindRun (branchRun above) fun above =>
  if above then pureRun true else
  bindRun (equalRealRun x tau) fun equal =>
  bindRun (branchRun equal) fun equal =>
  if equal then
    bindRun (ordinalRun i boundary) fun a =>
    bindRun (subNatRun boundary.length j) fun b =>
    bindRun (addNatRun a b) fun c =>
    bindRun (modNatRun c boundary.length) fun d => lessNatRun d s
  else pureRun false

def windowScanRun {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ) : Run (List (Fin m)) :=
  filterRun (windowMaskRun sigma tau boundary s j) (List.finRange m)

def frameFromListRun {m : ℕ} (V : Square m) (is : List (Fin m)) : Run (Rect m is.length) :=
  liftRun (Reference.TensorArithmeticExecution.vectorRun m fun i =>
    Reference.TensorArithmeticExecution.vectorRun is.length fun j =>
      Reference.TensorArithmeticExecution.readReal (V i (is.get j)))

end
end Reference.OrderedTensorExecution
