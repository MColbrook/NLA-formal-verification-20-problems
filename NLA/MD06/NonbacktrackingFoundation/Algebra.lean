module

public import NLA.MD06.NonbacktrackingFoundation.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06Nonbacktracking
open Reference.MD06CubicConfiguration
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_matching_left_mul {n : ℕ} (p : Pairing n)
    (B : Matrix (Dart n) (Dart n) ℝ) (a b : Dart n) :
    (MatchingMatrix p * B) a b = B (p.val a) b := by
  simp [Matrix.mul_apply,MatchingMatrix]

theorem actual_matching_square {n : ℕ} (p : Pairing n) :
    MatchingMatrix p * MatchingMatrix p = 1 := by
  ext a b
  rw [actual_matching_left_mul]
  simp only [MatchingMatrix,Matrix.one_apply]
  rw [p.property.1 a]

theorem actual_matching_trace_zero {n : ℕ} (p : Pairing n) :
    Matrix.trace (MatchingMatrix p)=0 := by
  simp [Matrix.trace,MatchingMatrix,p.property.2]

theorem actual_incidence_times_transpose (n : ℕ) :
    IncidenceMatrix n * (IncidenceMatrix n).transpose = (3 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext u v
  by_cases h : u=v
  · subst v
    simp [Matrix.mul_apply,IncidenceMatrix,Dart,Fintype.sum_prod_type]
  · simp [Matrix.mul_apply,IncidenceMatrix,Dart,Fintype.sum_prod_type,h]

theorem actual_transpose_incidence_entry {n : ℕ} (a b : Dart n) :
    ((IncidenceMatrix n).transpose * IncidenceMatrix n) a b = if a.1=b.1 then 1 else 0 := by
  simp [Matrix.mul_apply,IncidenceMatrix,eq_comm]

theorem actual_port_matrix_entry {n : ℕ} (a b : Dart n) :
    PortMatrix n a b = if a.1=b.1 ∧ a≠b then 1 else 0 := by
  rw [PortMatrix,Matrix.sub_apply,actual_transpose_incidence_entry,Matrix.one_apply]
  by_cases h : a=b
  · subst b;simp
  · by_cases hv : a.1=b.1
    · simp [h,hv]
    · simp [h,hv]

theorem actual_nonbacktracking_entry {n : ℕ} (p : Pairing n) (a b : Dart n) :
    NonbacktrackingMatrix p a b = if (p.val a).1=b.1 ∧ p.val a≠b then 1 else 0 := by
  rw [NonbacktrackingMatrix,actual_matching_left_mul,actual_port_matrix_entry]

#print axioms actual_matching_left_mul
#print axioms actual_matching_square
#print axioms actual_matching_trace_zero
#print axioms actual_incidence_times_transpose
#print axioms actual_transpose_incidence_entry
#print axioms actual_port_matrix_entry
#print axioms actual_nonbacktracking_entry
end Reference.MD06Nonbacktracking
