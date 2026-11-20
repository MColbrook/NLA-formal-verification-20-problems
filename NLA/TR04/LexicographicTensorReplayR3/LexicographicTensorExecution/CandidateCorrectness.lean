module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Literal candidate execution and its actual cyclic completion semantics. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.CandidateDefinitions
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.WindowBinding
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.FrameCopies
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorExecution
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary

theorem completeFrame_finCast {m k l n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (h : k=l) (rs : List ℕ) :
    completeFrame A (U.submatrix id ((finCongr h).symm)) rs=completeFrame A U rs := by
  subst l
  rfl

theorem actual_cyclic_candidate_execution {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount (denseTensor A) tau)) (rs : List ℕ) :
    (cyclicExecutionRun A (leftVectorMatrix (denseTensor A)) (sigmaOf (denseTensor A))
      tau s j.val rs).value=
      completeFrame A (candidateFrame (denseTensor A) tau s j) rs := by
  simp only [cyclicExecutionRun,value_bind,value_lift,
    Reference.LexTensorArithmeticExecution.actual_named_completeFrame_execution]
  rw [actual_window_scan_value (denseTensor A) tau s j]
  have h := completeFrame_finCast A
    (frameFromListRun (leftVectorMatrix (denseTensor A))
      (Reference.LexOrderedIndex.indexList (selected (denseTensor A) tau s j))).value
    (Reference.LexOrderedIndex.indexList_length (selected (denseTensor A) tau s j)) rs
  rw [actual_indicator_frame_copy] at h
  exact h.symm

#print axioms completeFrame_finCast
#print axioms actual_cyclic_candidate_execution
end
end Reference.LexTensorExecution
