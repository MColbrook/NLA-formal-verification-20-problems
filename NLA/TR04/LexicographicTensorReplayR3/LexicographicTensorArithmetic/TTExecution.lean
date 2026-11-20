module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Named recursive TT-SVD execution with exact actual subspace and scalar instructions. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorArithmetic.TensorOperations

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.LexTensorCompletion
open scoped Matrix

theorem actual_named_ttSVD_execution (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) :
    (ttRun m ns A rs).value=ttSVD m ns A rs := by
  induction ns generalizing m rs with
  | nil => simp only [ttRun,ttSVD,value_pure]
  | cons n ns ih =>
    cases rs with
    | nil => simp only [ttRun,ttSVD,value_pure]
    | cons r rs =>
      simp only [ttRun,value_bind,frameRun_value,tensorMulRun_value,tensorCopyRun_value,ih,ttSVD]

theorem actual_named_completeFrame_execution {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) :
    (completionRun A U rs).value=completeFrame A U rs := by
  simp only [completionRun,value_bind,tensorMulRun_value,tensorCopyRun_value,actual_named_ttSVD_execution,completeFrame]

#print axioms actual_named_ttSVD_execution
#print axioms actual_named_completeFrame_execution
end
end Reference.LexTensorArithmeticExecution
