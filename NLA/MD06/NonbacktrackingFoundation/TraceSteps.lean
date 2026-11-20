module

public import NLA.MD06.NonbacktrackingFoundation.PowerLift
public import NLA.MD06.NonbacktrackingFoundation.TraceDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Nonbacktracking
open Reference.MD06CubicConfiguration

theorem actual_nonbacktracking_split {n : ℕ} (p : Pairing n) :
    NonbacktrackingMatrix p = LiftMatrix p * IncidenceMatrix n - MatchingMatrix p := by
  simp only [NonbacktrackingMatrix,PortMatrix,Matrix.mul_sub,Matrix.mul_one,
    LiftMatrix,Matrix.mul_assoc]

theorem actual_incidence_lift {n : ℕ} (p : Pairing n) :
    IncidenceMatrix n * LiftMatrix p = AdjacencyMatrix p := by
  simp only [LiftMatrix,AdjacencyMatrix,Matrix.mul_assoc]

theorem actual_incidence_reverse_lift {n : ℕ} (p : Pairing n) :
    IncidenceMatrix n * (MatchingMatrix p * LiftMatrix p) = (3 : ℝ) • 1 := by
  rw [actual_matching_lift,actual_incidence_times_transpose]

theorem actual_trace_step {n : ℕ} (p : Pairing n) (t : ℕ) :
    Matrix.trace (NonbacktrackingMatrix p ^ (t+1)) =
      Matrix.trace (AdjacencyMatrix p * (LiftCoefficients (AdjacencyMatrix p) t).1 -
        (3 : ℝ) • (LiftCoefficients (AdjacencyMatrix p) t).2) -
      Matrix.trace (NonbacktrackingMatrix p ^ t * MatchingMatrix p) := by
  calc
    _ = Matrix.trace ((NonbacktrackingMatrix p ^ t * LiftMatrix p) * IncidenceMatrix n -
        NonbacktrackingMatrix p ^ t * MatchingMatrix p) := by
      rw [pow_succ,actual_nonbacktracking_split,Matrix.mul_sub,← Matrix.mul_assoc]
    _ = Matrix.trace (IncidenceMatrix n * (NonbacktrackingMatrix p ^ t * LiftMatrix p)) -
        Matrix.trace (NonbacktrackingMatrix p ^ t * MatchingMatrix p) := by
      rw [Matrix.trace_sub,Matrix.trace_mul_comm]
    _ = _ := by
      rw [actual_nonbacktracking_power_lift,Matrix.mul_sub,← Matrix.mul_assoc,
        actual_incidence_lift,← Matrix.mul_assoc,actual_incidence_reverse_lift,
        Matrix.smul_mul,Matrix.one_mul]

theorem actual_reverse_trace_step {n : ℕ} (p : Pairing n) (t : ℕ) :
    Matrix.trace (NonbacktrackingMatrix p ^ (t+1) * MatchingMatrix p) =
      Matrix.trace ((3 : ℝ) • (LiftCoefficients (AdjacencyMatrix p) t).1 -
        AdjacencyMatrix p * (LiftCoefficients (AdjacencyMatrix p) t).2) -
      Matrix.trace (NonbacktrackingMatrix p ^ t) := by
  have hs : NonbacktrackingMatrix p * MatchingMatrix p =
      LiftMatrix p * (IncidenceMatrix n * MatchingMatrix p) - 1 := by
    rw [actual_nonbacktracking_split,Matrix.sub_mul,actual_matching_square,Matrix.mul_assoc]
  calc
    _ = Matrix.trace ((NonbacktrackingMatrix p ^ t * LiftMatrix p) *
        (IncidenceMatrix n * MatchingMatrix p) - NonbacktrackingMatrix p ^ t) := by
      rw [pow_succ,Matrix.mul_assoc,hs,Matrix.mul_sub,Matrix.mul_one,← Matrix.mul_assoc]
    _ = Matrix.trace ((IncidenceMatrix n * MatchingMatrix p) *
        (NonbacktrackingMatrix p ^ t * LiftMatrix p)) -
        Matrix.trace (NonbacktrackingMatrix p ^ t) := by
      rw [Matrix.trace_sub,Matrix.trace_mul_comm]
    _ = _ := by
      rw [actual_nonbacktracking_power_lift,Matrix.mul_sub]
      have h1 : (IncidenceMatrix n * MatchingMatrix p) * LiftMatrix p = (3 : ℝ) • 1 := by
        rw [Matrix.mul_assoc,actual_incidence_reverse_lift]
      have h2 : (IncidenceMatrix n * MatchingMatrix p) * (MatchingMatrix p * LiftMatrix p) =
          AdjacencyMatrix p := by
        rw [Matrix.mul_assoc,← Matrix.mul_assoc (MatchingMatrix p),actual_matching_square,
          Matrix.one_mul,actual_incidence_lift]
      rw [← Matrix.mul_assoc,h1,Matrix.smul_mul,Matrix.one_mul,← Matrix.mul_assoc,h2]

#print axioms actual_nonbacktracking_split

#print axioms actual_incidence_lift

#print axioms actual_incidence_reverse_lift

#print axioms actual_trace_step

#print axioms actual_reverse_trace_step
end Reference.MD06Nonbacktracking
