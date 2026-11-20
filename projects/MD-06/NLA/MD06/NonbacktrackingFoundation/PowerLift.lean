module

public import NLA.MD06.NonbacktrackingFoundation.Lifts

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Nonbacktracking
open Reference.MD06CubicConfiguration

theorem actual_nonbacktracking_power_lift {n : ℕ} (p : Pairing n) (t : ℕ) :
    NonbacktrackingMatrix p ^ t * LiftMatrix p =
      LiftMatrix p * (LiftCoefficients (AdjacencyMatrix p) t).1 -
      (MatchingMatrix p * LiftMatrix p) * (LiftCoefficients (AdjacencyMatrix p) t).2 := by
  induction t with
  | zero => simp [LiftCoefficients]
  | succ t ih =>
    rw [pow_succ', Matrix.mul_assoc, ih, Matrix.mul_sub,
      ← Matrix.mul_assoc, actual_nonbacktracking_lift, Matrix.sub_mul,
      ← Matrix.mul_assoc (NonbacktrackingMatrix p), actual_nonbacktracking_reverse_lift]
    simp only [LiftCoefficients, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
    module

#print axioms actual_nonbacktracking_power_lift
end Reference.MD06Nonbacktracking
