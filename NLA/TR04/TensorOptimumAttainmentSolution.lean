module

public import NLA.TR04.TensorOptimumAttainment.OptimalBound
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorOptimumAttainment
noncomputable section
open Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection

theorem verified_actual_tensor_feasible_isClosed (m : ℕ) (ns rs : List ℕ) :
    IsClosed (feasibleSet m ns rs) := by
  exact actual_tensor_feasible_isClosed m ns rs

theorem verified_actual_zero_tensor_feasible (m : ℕ) (ns rs : List ℕ) (hlen : rs.length=ns.length) :
    feasible m ns (0 : Tensor m ns) rs := by
  exact actual_zero_tensor_feasible m ns rs hlen

theorem verified_actual_best_feasible_tensor_exists {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (rs : List ℕ) (hlen : rs.length=ns.length) :
    ∃ B : Tensor m ns, feasible m ns B rs ∧
      ∀ Y : Tensor m ns, feasible m ns Y rs → error A B≤error A Y := by
  exact actual_best_feasible_tensor_exists A rs hlen

theorem verified_actual_optimal_error_attained {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (rs : List ℕ) (hlen : rs.length=ns.length) :
    ∃ B : Tensor m ns, feasible m ns B rs ∧ error A B=optimalError A rs ∧
      ∀ Y : Tensor m ns, feasible m ns Y rs → error A B≤error A Y := by
  exact actual_optimal_error_attained A rs hlen

theorem verified_actual_optimal_error_nonneg {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (rs : List ℕ) (hlen : rs.length=ns.length) : 0≤optimalError A rs := by
  exact actual_optimal_error_nonneg A rs hlen

theorem verified_actual_optimal_error_zero_iff_feasible {m : ℕ} {ns : List ℕ} (A : Tensor m ns)
    (rs : List ℕ) (hlen : rs.length=ns.length) :
    optimalError A rs=0 ↔ feasible m ns A rs := by
  exact actual_optimal_error_zero_iff_feasible A rs hlen

theorem verified_actual_solver_with_genuine_feasible_minimum {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 0<m) :
    feasible m (n::ns) (solver A r rs) (r::rs) ∧ (candidates A r rs).length≤m ∧
      (0<optimalError A (r::rs) → error A (solver A r rs)<((ns.length : ℝ)+1)*optimalError A (r::rs)) ∧
      (optimalError A (r::rs)=0 → solver A r rs=A) := by
  exact actual_solver_with_genuine_feasible_minimum A r rs hlen hr hns hm

#print axioms Reference.TensorOptimumAttainment.verified_actual_tensor_feasible_isClosed
#print axioms Reference.TensorOptimumAttainment.verified_actual_zero_tensor_feasible
#print axioms Reference.TensorOptimumAttainment.verified_actual_best_feasible_tensor_exists
#print axioms Reference.TensorOptimumAttainment.verified_actual_optimal_error_attained
#print axioms Reference.TensorOptimumAttainment.verified_actual_optimal_error_nonneg
#print axioms Reference.TensorOptimumAttainment.verified_actual_optimal_error_zero_iff_feasible
#print axioms Reference.TensorOptimumAttainment.verified_actual_solver_with_genuine_feasible_minimum
end
end Reference.TensorOptimumAttainment
