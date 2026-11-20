module

public import NLA.TR04.TensorArithmeticExecutionReplayR3.PolynomialCharge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorArithmeticExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion Reference.TensorCandidateSelection Reference.CyclicBoundary
open scoped BigOperators Matrix

theorem verified_matrixMulRun_value {m k n : ℕ} (A : Rect m k) (B : Rect k n) :
    (matrixMulRun A B).value=A*B := by
  exact matrixMulRun_value A B

theorem verified_actual_dense_multiplication_charge {m k n : ℕ} (A : Rect m k) (B : Rect k n) :
    charge (matrixMulRun A B)=m*n*(4*k+1) := by
  exact actual_dense_multiplication_charge A B

theorem verified_tensorErrorRun_value {m : ℕ} {ns : List ℕ} (A B : Tensor m ns) :
    (tensorErrorRun A B).value=error A B := by
  exact tensorErrorRun_value A B

theorem verified_actual_squared_entry_error_execution_charge {m : ℕ} {ns : List ℕ} (A B : Tensor m ns) :
    charge (tensorErrorRun A B)=m*(5*Fintype.card (ModeIndex ns)+2)+1 := by
  exact actual_squared_entry_error_execution_charge A B

theorem verified_actual_first_minimum_execution {m : ℕ} {ns : List ℕ} (A x : Tensor m ns)
    (xs : List (Tensor m ns)) : (minimumRun A x xs).value=firstMinimum A x xs := by
  exact actual_first_minimum_execution A x xs

theorem verified_actual_first_minimum_execution_charge {m : ℕ} {ns : List ℕ} (A x : Tensor m ns)
    (xs : List (Tensor m ns)) :
    charge (minimumRun A x xs)=xs.length*(2*(m*(5*Fintype.card (ModeIndex ns)+2)+1)+1) := by
  exact actual_first_minimum_execution_charge A x xs

theorem verified_actual_solver_selection_stage_execution {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) :
    (selectionStageRun A r rs).value=solver A r rs := by
  exact actual_solver_selection_stage_execution A r rs

theorem verified_actual_solver_selection_stage_polynomial_charge {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 0<m) :
    charge (selectionStageRun A r rs)≤m*(2*(m*(5*Fintype.card (ModeIndex (n::ns))+2)+1)+1) := by
  exact actual_solver_selection_stage_polynomial_charge A r rs hm

theorem verified_tensorMulRun_value {m k : ℕ} {ns : List ℕ} (V : Rect m k) (A : Tensor k ns) :
    (tensorMulRun V A).value=V*A := by
  exact tensorMulRun_value V A

theorem verified_tensorMulRun_charge {m k : ℕ} {ns : List ℕ} (V : Rect m k) (A : Tensor k ns) :
    charge (tensorMulRun V A)=m*Fintype.card (ModeIndex ns)*(4*k+1) := by
  exact tensorMulRun_charge V A

theorem verified_frameRun_value {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) :
    (frameRun A r).value=svdFrame A r := by
  exact frameRun_value A r

theorem verified_actual_exact_subspace_primitive_is_valid {m n : ℕ} (A : Rect m n) :
    IsOrthogonal (leftSubspace A).value ∧
    (leftSubspace A).value.transpose*(A*A.transpose)*(leftSubspace A).value=
      Matrix.diagonal (fun i : Fin m => singularValue A.transpose i.val^2) := by
  exact actual_exact_subspace_primitive_is_valid A

theorem verified_actual_named_ttSVD_execution (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) :
    (ttRun m ns A rs).value=ttSVD m ns A rs := by
  exact actual_named_ttSVD_execution m ns A rs

theorem verified_actual_named_completeFrame_execution {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) :
    (completionRun A U rs).value=completeFrame A U rs := by
  exact actual_named_completeFrame_execution A U rs

theorem verified_actual_ttSVD_trace_charge (m : ℕ) (ns : List ℕ) (A : Tensor m ns) (rs : List ℕ) :
    charge (ttRun m ns A rs)=ttCharge m ns rs := by
  exact actual_ttSVD_trace_charge m ns A rs

theorem verified_actual_completeFrame_trace_charge {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) :
    charge (completionRun A U rs)=
      k*modeCard (n::ns)*(4*m+1)+rowCount k n*modeCard ns+
      ttCharge (rowCount k n) ns rs+k*modeCard (n::ns)+m*modeCard (n::ns)*(4*k+1) := by
  exact actual_completeFrame_trace_charge A U rs

theorem verified_actual_ttSVD_uniform_shape_charge (m : ℕ) (ns rs : List ℕ) (B : ℕ)
    (hB : 1≤B) (hmode : ∀ n∈ns,1≤n)
    (hsize : m*modeCard ns≤B) (hcols : modeCard ns≤B) :
    ttCharge m ns rs≤ns.length*40*B^3 := by
  exact actual_ttSVD_uniform_shape_charge m ns rs B hB hmode hsize hcols

theorem verified_actual_completeFrame_uniform_shape_charge {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) (B : ℕ)
    (hB : 1≤B) (hmode : ∀ a∈n::ns,1≤a) (hk : k≤m)
    (hsize : m*modeCard (n::ns)≤B) (hcols : modeCard (n::ns)≤B) :
    charge (completionRun A U rs)≤(ns.length*40+12)*B^3 := by
  exact actual_completeFrame_uniform_shape_charge A U rs B hB hmode hk hsize hcols

theorem verified_actual_ttSVD_dense_polynomial_charge (m : ℕ) (ns : List ℕ) (A : Tensor m ns)
    (rs : List ℕ) (hm : 1≤m) (hmode : ∀ n∈ns,2≤n) :
    charge (ttRun m ns A rs)≤1080*(denseSize m ns)^4 := by
  exact actual_ttSVD_dense_polynomial_charge m ns A rs hm hmode

theorem verified_actual_completeFrame_dense_polynomial_charge {m k n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (rs : List ℕ) (hm : 1≤m)
    (hk : k≤m) (hmode : ∀ a∈n::ns,2≤a) :
    charge (completionRun A U rs)≤1404*(denseSize m (n::ns))^4 := by
  exact actual_completeFrame_dense_polynomial_charge A U rs hm hk hmode

#print axioms Reference.TensorArithmeticExecution.verified_matrixMulRun_value
#print axioms Reference.TensorArithmeticExecution.verified_actual_dense_multiplication_charge
#print axioms Reference.TensorArithmeticExecution.verified_tensorErrorRun_value
#print axioms Reference.TensorArithmeticExecution.verified_actual_squared_entry_error_execution_charge
#print axioms Reference.TensorArithmeticExecution.verified_actual_first_minimum_execution
#print axioms Reference.TensorArithmeticExecution.verified_actual_first_minimum_execution_charge
#print axioms Reference.TensorArithmeticExecution.verified_actual_solver_selection_stage_execution
#print axioms Reference.TensorArithmeticExecution.verified_actual_solver_selection_stage_polynomial_charge
#print axioms Reference.TensorArithmeticExecution.verified_tensorMulRun_value
#print axioms Reference.TensorArithmeticExecution.verified_tensorMulRun_charge
#print axioms Reference.TensorArithmeticExecution.verified_frameRun_value
#print axioms Reference.TensorArithmeticExecution.verified_actual_exact_subspace_primitive_is_valid
#print axioms Reference.TensorArithmeticExecution.verified_actual_named_ttSVD_execution
#print axioms Reference.TensorArithmeticExecution.verified_actual_named_completeFrame_execution
#print axioms Reference.TensorArithmeticExecution.verified_actual_ttSVD_trace_charge
#print axioms Reference.TensorArithmeticExecution.verified_actual_completeFrame_trace_charge
#print axioms Reference.TensorArithmeticExecution.verified_actual_ttSVD_uniform_shape_charge
#print axioms Reference.TensorArithmeticExecution.verified_actual_completeFrame_uniform_shape_charge
#print axioms Reference.TensorArithmeticExecution.verified_actual_ttSVD_dense_polynomial_charge
#print axioms Reference.TensorArithmeticExecution.verified_actual_completeFrame_dense_polynomial_charge
end
end Reference.TensorArithmeticExecution
