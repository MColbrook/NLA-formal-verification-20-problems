module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Actual ordered traversal, prefix copying, and bounded spectrum lookup. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.ProgramDefinitions
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.FrameCopies
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexTensorCompletion

@[simp] theorem listMapRun_value {α β : Type} (f : α → Run β) (xs : List α) :
    (listMapRun f xs).value=xs.map (fun x => (f x).value) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [listMapRun,ih]

theorem listMapRun_charge {α β : Type} (f : α → Run β) (xs : List α) (C : ℕ)
    (h : ∀ x∈xs,charge (f x)≤C) : charge (listMapRun f xs)≤xs.length*C := by
  induction xs with
  | nil => simp [listMapRun]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [listMapRun,charge_bind,charge_pure,List.length_cons]
      nlinarith

theorem prefixFrameRun_value {m : ℕ} (V : Square m) (k : ℕ) :
    (prefixFrameRun V k).value=fun i j =>
      V i ⟨j.val,lt_of_lt_of_le j.isLt (Nat.min_le_right k m)⟩ := by
  simp only [prefixFrameRun,value_lift,Reference.LexTensorArithmeticExecution.vectorRun_value,
    Reference.LexTensorArithmeticExecution.value_read]

theorem prefixFrameRun_charge {m : ℕ} (V : Square m) (k : ℕ) :
    charge (prefixFrameRun V k)=m*min k m := by
  simp only [prefixFrameRun,charge_lift]
  rw [Reference.LexTensorArithmeticExecution.vectorRun_charge]
  simp_rw [Reference.LexTensorArithmeticExecution.vectorRun_charge,
    Reference.LexTensorArithmeticExecution.charge_read]
  simp

theorem actual_prefix_completion_execution {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (k : ℕ) (rs : List ℕ) :
    (prefixCompletionRun A (leftVectorMatrix (denseTensor A)) k rs).value=
      completeFrame A (svdFrame A k) rs := by
  simp only [prefixCompletionRun,value_bind,value_lift,
    Reference.LexTensorArithmeticExecution.actual_named_completeFrame_execution,
    prefixFrameRun_value]
  rfl

theorem sigmaAtRun_value {m : ℕ} (sigma : Fin m → ℝ) (a : ℕ) :
    (sigmaAtRun sigma a).value=if h:a<m then sigma ⟨a,h⟩ else 0 := by
  by_cases ha : a<m
  · simp [sigmaAtRun,lessNatRun,branchRun,readRun,ha,liftRun]
  · simp [sigmaAtRun,lessNatRun,branchRun,ha,liftRun,Reference.LexTensorArithmeticExecution.zeroReal]

theorem sigmaAtRun_charge {m : ℕ} (sigma : Fin m → ℝ) (a : ℕ) :
    charge (sigmaAtRun sigma a)=3 := by
  by_cases ha : a<m
  · simp [sigmaAtRun,lessNatRun,branchRun,readRun,ha,charge,liftRun,
      Reference.LexTensorArithmeticExecution.readReal,eventCharge,Reference.LexTensorArithmeticExecution.eventCharge]
  · simp [sigmaAtRun,lessNatRun,branchRun,ha,charge,liftRun,
      Reference.LexTensorArithmeticExecution.zeroReal,eventCharge,Reference.LexTensorArithmeticExecution.eventCharge]

#print axioms listMapRun_value
#print axioms listMapRun_charge
#print axioms actual_prefix_completion_execution
#print axioms prefixFrameRun_charge
#print axioms sigmaAtRun_value
#print axioms sigmaAtRun_charge
end
end Reference.LexTensorExecution
