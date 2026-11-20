module

/- Actual window scanning, copied frames and named recursive completion execution. -/
public import NLA.TR04.OrderedTensorExecution.ScanDefinitions
public import NLA.TR04.TensorArithmeticExecution.TTExecution

@[expose] public section

set_option autoImplicit false
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion

def cyclicExecutionRun {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (V : Square m) (sigma : Fin m → ℝ) (tau : ℝ) (s j : ℕ) (rs : List ℕ) :
    Run (Tensor m (n::ns)) :=
  bindRun (equalScanRun sigma tau) fun boundary =>
  bindRun (windowScanRun sigma tau boundary s j) fun indices =>
  bindRun (frameFromListRun V indices) fun U =>
  liftRun (Reference.TensorArithmeticExecution.completionRun A U rs)

end
end Reference.OrderedTensorExecution
