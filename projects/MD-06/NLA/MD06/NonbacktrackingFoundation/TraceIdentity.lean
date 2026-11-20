module

public import NLA.MD06.NonbacktrackingFoundation.TraceSteps
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Nonbacktracking
open Reference.MD06CubicConfiguration

theorem actual_trace_polynomial_successor {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) :
    TracePolynomial A (t+1) = A * (LiftCoefficients A t).1 -
      (4 : ℝ) • (LiftCoefficients A t).2 := by
  simp only [TracePolynomial,LiftCoefficients]
  module

theorem actual_trace_polynomial_recurrence {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (t : ℕ) :
    TracePolynomial A (t+2) = A * TracePolynomial A (t+1) - (2 : ℝ) • TracePolynomial A t := by
  rw [actual_trace_polynomial_successor A (t+1), actual_trace_polynomial_successor A t]
  simp only [LiftCoefficients,TracePolynomial,Matrix.mul_sub,Matrix.mul_smul]
  module

theorem actual_nonbacktracking_trace_identity {n : ℕ} (p : Pairing n) (t : ℕ) :
    Matrix.trace (NonbacktrackingMatrix p ^ t) =
      Matrix.trace (TracePolynomial (AdjacencyMatrix p) t) + (TraceOffsets n t).1 ∧
    Matrix.trace (NonbacktrackingMatrix p ^ t * MatchingMatrix p) =
      Matrix.trace ((LiftCoefficients (AdjacencyMatrix p) t).2) - (TraceOffsets n t).2 := by
  induction t with
  | zero =>
    constructor
    · simp only [pow_zero,TracePolynomial,LiftCoefficients,TraceOffsets,
        Matrix.mul_zero,sub_zero,Matrix.trace_smul,Matrix.trace_one,
        Fintype.card_prod,Fintype.card_fin,Dart]
      push_cast
      ring
    · simp [LiftCoefficients,TraceOffsets,actual_matching_trace_zero]
  | succ t ih =>
    rcases ih with ⟨ht,hu⟩
    constructor
    · rw [actual_trace_step,hu,actual_trace_polynomial_successor]
      simp only [TraceOffsets,Matrix.trace_sub,Matrix.trace_smul]
      ring
    · rw [actual_reverse_trace_step,ht]
      simp only [TraceOffsets,LiftCoefficients,TracePolynomial,Matrix.trace_sub,Matrix.trace_smul]
      ring

theorem actual_trace_offset_bounds (n t : ℕ) :
    (0 ≤ (TraceOffsets n t).1 ∧ (TraceOffsets n t).1 ≤ n) ∧
    (0 ≤ (TraceOffsets n t).2 ∧ (TraceOffsets n t).2 ≤ n) := by
  induction t with
  | zero => simp [TraceOffsets]
  | succ t ih => exact ⟨ih.2,ih.1⟩

theorem actual_nonbacktracking_trace_bounds {n : ℕ} (p : Pairing n) (t : ℕ) :
    Matrix.trace (TracePolynomial (AdjacencyMatrix p) t) ≤
      Matrix.trace (NonbacktrackingMatrix p ^ t) ∧
    Matrix.trace (NonbacktrackingMatrix p ^ t) ≤
      Matrix.trace (TracePolynomial (AdjacencyMatrix p) t) + n := by
  rw [(actual_nonbacktracking_trace_identity p t).1]
  exact ⟨le_add_of_nonneg_right (actual_trace_offset_bounds n t).1.1,
    add_le_add (le_refl _) (actual_trace_offset_bounds n t).1.2⟩

#print axioms actual_trace_polynomial_successor

#print axioms actual_trace_polynomial_recurrence

#print axioms actual_nonbacktracking_trace_identity

#print axioms actual_trace_offset_bounds

#print axioms actual_nonbacktracking_trace_bounds
end Reference.MD06Nonbacktracking
