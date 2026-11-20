module

/- Named recursive TT-SVD execution with exact actual subspace and scalar instructions. -/
public import NLA.TR04.TensorArithmeticExecution.TensorOperations

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.TensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.RecursiveTensorCompletion
open scoped Matrix

def ttRun (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) : Run (Tensor m ns) :=
  match ns,A,rs with
  | [],A,_ => pureRun A
  | _::_,A,[] => pureRun A
  | n::ns,A,r::rs =>
    bindRun (frameRun A r) fun U =>
    bindRun (tensorMulRun U.transpose A) fun C0 =>
    bindRun (tensorCopyRun (merge C0)) fun C =>
    bindRun (ttRun (rowCount (min r m) n) ns C rs) fun Z =>
    bindRun (tensorCopyRun (unmerge (m:=min r m) (n:=n) Z)) fun Z0 =>
    tensorMulRun U Z0
termination_by ns.length

theorem actual_named_ttSVD_execution (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) :
    (ttRun m ns A rs).value=ttSVD m ns A rs := by
  induction ns generalizing m rs with
  | nil => simp only [ttRun,ttSVD,value_pure]
  | cons n ns ih =>
    cases rs with
    | nil => simp only [ttRun,ttSVD,value_pure]
    | cons r rs =>
      simp only [ttRun,value_bind,frameRun_value,tensorMulRun_value,tensorCopyRun_value,ih,ttSVD]

def completionRun {m k n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns))
    (U : Rect m k) (rs : List ℕ) : Run (Tensor m (n::ns)) :=
  bindRun (tensorMulRun U.transpose A) fun C0 =>
  bindRun (tensorCopyRun (merge C0)) fun C =>
  bindRun (ttRun (rowCount k n) ns C rs) fun Z =>
  bindRun (tensorCopyRun (unmerge (m:=k) (n:=n) Z)) fun Z0 => tensorMulRun U Z0

theorem actual_named_completeFrame_execution {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) :
    (completionRun A U rs).value=completeFrame A U rs := by
  simp only [completionRun,value_bind,tensorMulRun_value,tensorCopyRun_value,actual_named_ttSVD_execution,completeFrame]

#print axioms actual_named_ttSVD_execution
#print axioms actual_named_completeFrame_execution
end
end Reference.TensorArithmeticExecution
