module

public import NLA.MD06.NonbacktrackingFoundation.Algebra
public import NLA.MD06.NonbacktrackingFoundation.LiftDefinitions
public import Mathlib.Tactic.Module

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Nonbacktracking
open Reference.MD06CubicConfiguration

theorem actual_matching_lift {n : ℕ} (p : Pairing n) :
    MatchingMatrix p * LiftMatrix p = (IncidenceMatrix n).transpose := by
  rw [LiftMatrix, ← Matrix.mul_assoc, actual_matching_square, Matrix.one_mul]

theorem actual_nonbacktracking_lift {n : ℕ} (p : Pairing n) :
    NonbacktrackingMatrix p * LiftMatrix p =
      LiftMatrix p * AdjacencyMatrix p - MatchingMatrix p * LiftMatrix p := by
  rw [NonbacktrackingMatrix, PortMatrix, Matrix.mul_sub, Matrix.mul_one,
    Matrix.sub_mul, LiftMatrix, AdjacencyMatrix]
  simp only [Matrix.mul_assoc]

theorem actual_nonbacktracking_reverse_lift {n : ℕ} (p : Pairing n) :
    NonbacktrackingMatrix p * (MatchingMatrix p * LiftMatrix p) = (2 : ℝ) • LiftMatrix p := by
  rw [actual_matching_lift, NonbacktrackingMatrix, PortMatrix, Matrix.mul_sub,
    Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, actual_incidence_times_transpose,
    Matrix.mul_smul, Matrix.mul_one, LiftMatrix]
  simp only [Matrix.mul_smul]
  module

#print axioms actual_matching_lift
#print axioms actual_nonbacktracking_lift
#print axioms actual_nonbacktracking_reverse_lift
end Reference.MD06Nonbacktracking
