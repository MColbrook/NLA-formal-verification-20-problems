module

/- First-minimum selection is an actual interpreted finite loop over computed candidates.
This module verifies the selection stage; candidate generation is not charged here. -/
public import NLA.TR04.TensorArithmeticExecution.ErrorLoops

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.TensorArithmeticExecution
noncomputable section
open Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection

def minimumRun {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (x : Tensor m ns) :
    List (Tensor m ns) → Run (Tensor m ns)
  | [] => pureRun x
  | y::ys => bindRun (tensorErrorRun A y) fun ey =>
      bindRun (tensorErrorRun A x) fun ex =>
      bindRun (lessReal ey ex) fun better =>
      if better then minimumRun A y ys else minimumRun A x ys

theorem actual_first_minimum_execution {m : ℕ} {ns : List ℕ} (A x : Tensor m ns)
    (xs : List (Tensor m ns)) : (minimumRun A x xs).value=firstMinimum A x xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : error A y<error A x
    · simp [minimumRun,value_bind,tensorErrorRun_value,value_less,h,firstMinimum,ih]
    · simp [minimumRun,value_bind,tensorErrorRun_value,value_less,h,firstMinimum,ih]

theorem actual_first_minimum_execution_charge {m : ℕ} {ns : List ℕ} (A x : Tensor m ns)
    (xs : List (Tensor m ns)) :
    charge (minimumRun A x xs)=xs.length*(2*(m*(5*Fintype.card (ModeIndex ns)+2)+1)+1) := by
  induction xs generalizing x with
  | nil => simp [minimumRun]
  | cons y ys ih =>
    simp only [minimumRun,charge_bind,actual_squared_entry_error_execution_charge,charge_less]
    split <;> rw [ih] <;> simp only [List.length_cons,Nat.add_mul,Nat.one_mul] <;> omega

def selectionStageRun {m n : ℕ} {ns : List ℕ} (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :
    Run (Tensor m (n::ns)) :=
  match candidates A r rs with
  | [] => pureRun (leadingCompletion A r rs)
  | x::xs => minimumRun A x xs

theorem actual_solver_selection_stage_execution {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :
    (selectionStageRun A r rs).value=solver A r rs := by
  cases h : candidates A r rs with
  | nil => simp [selectionStageRun,solver,h]
  | cons x xs => simp only [selectionStageRun,solver,h,actual_first_minimum_execution]

theorem actual_solver_selection_stage_polynomial_charge {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 0<m) :
    charge (selectionStageRun A r rs)≤m*(2*(m*(5*Fintype.card (ModeIndex (n::ns))+2)+1)+1) := by
  unfold selectionStageRun
  split
  · simp only [charge_pure];omega
  · rw [actual_first_minimum_execution_charge]
    have hc := actual_completion_count_le_first_mode A r rs hm
    rename_i x xs he
    rw [he] at hc
    have hlen : xs.length≤m := by simpa using (Nat.le_of_succ_le hc)
    exact Nat.mul_le_mul_right _ hlen

#print axioms actual_first_minimum_execution
#print axioms actual_first_minimum_execution_charge
#print axioms actual_solver_selection_stage_execution
#print axioms actual_solver_selection_stage_polynomial_charge
end
end Reference.TensorArithmeticExecution
