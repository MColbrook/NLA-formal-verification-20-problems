module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Actual scalar-read frame copies, with entrywise semantics and derived charge. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.ScanChecks
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorExecution
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.LexOrderedCyclicBoundary
open scoped BigOperators

theorem frameFromListRun_value {m : ℕ} (V : Square m) (is : List (Fin m)) :
    (frameFromListRun V is).value=fun i j => V i (is.get j) := by
  simp only [frameFromListRun,value_lift,Reference.LexTensorArithmeticExecution.vectorRun_value,
    Reference.LexTensorArithmeticExecution.value_read]

theorem frameFromListRun_charge {m : ℕ} (V : Square m) (is : List (Fin m)) :
    charge (frameFromListRun V is)=m*is.length := by
  simp only [frameFromListRun,charge_lift]
  rw [Reference.LexTensorArithmeticExecution.vectorRun_charge]
  simp_rw [Reference.LexTensorArithmeticExecution.vectorRun_charge,
    Reference.LexTensorArithmeticExecution.charge_read]
  simp

theorem actual_indicator_frame_copy {m : ℕ} (V : Square m) (p : Fin m → Prop) :
    ((frameFromListRun V (Reference.LexOrderedIndex.indexList p)).value).submatrix id
      ((finCongr (Reference.LexOrderedIndex.indexList_length p)).symm)=indicatorFrame V p := by
  rw [frameFromListRun_value]
  rfl

#print axioms frameFromListRun_value
#print axioms frameFromListRun_charge
#print axioms actual_indicator_frame_copy
end
end Reference.LexTensorExecution
