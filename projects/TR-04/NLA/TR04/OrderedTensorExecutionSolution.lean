module

public import NLA.TR04.OrderedTensorExecution.GenuineProgramOptimal
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reference.OrderedTensorExecution
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion Reference.OrderedCyclicBoundary Reference.OrderedTensorSolver Reference.TensorOptimumAttainment
open scoped BigOperators Matrix

theorem verified_actual_cyclic_execution_charge : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (sigma : Fin m → ℝ)
    (tau : ℝ) (s j : ℕ) (rs : List ℕ) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a),
  charge (cyclicExecutionRun A V sigma tau s j rs) ≤
      4*m*m+13*m+1404*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^4 := actual_cyclic_execution_charge

theorem verified_actual_cyclic_execution_dense_polynomial_charge : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (sigma : Fin m → ℝ)
    (tau : ℝ) (s j : ℕ) (rs : List ℕ) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a),
  charge (cyclicExecutionRun A V sigma tau s j rs) ≤
      1421*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^4 := actual_cyclic_execution_dense_polynomial_charge

theorem verified_completeFrame_finCast : ∀ {m k l n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (U : Rect m k) (h : k=l) (rs : List ℕ),
  completeFrame A (U.submatrix id ((finCongr h).symm)) rs=completeFrame A U rs := completeFrame_finCast

theorem verified_actual_cyclic_candidate_execution : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (tau : ℝ) (s : ℕ)
    (j : Fin (eCount (denseTensor A) tau)) (rs : List ℕ),
  (cyclicExecutionRun A (leftVectorMatrix (denseTensor A)) (sigmaOf (denseTensor A))
      tau s j.val rs).value=
      completeFrame A (candidateFrame (denseTensor A) tau s j) rs := actual_cyclic_candidate_execution

theorem verified_filterRun_value : ∀ {α : Type} (p : α → Run Bool) (xs : List α),
  (filterRun p xs).value=xs.filter (fun i => (p i).value) := filterRun_value

theorem verified_filterRun_charge : ∀ {α : Type} (p : α → Run Bool) (xs : List α) (C : ℕ)
    (h : ∀ i ∈ xs, charge (p i) ≤ C),
  charge (filterRun p xs) ≤ xs.length*(C+1) := filterRun_charge

theorem verified_ordinalRun_value : ∀ {m : ℕ} (i : Fin m) (xs : List (Fin m)),
  (ordinalRun i xs).value=xs.idxOf i := ordinalRun_value

theorem verified_ordinalRun_charge : ∀ {m : ℕ} (i : Fin m) (xs : List (Fin m)),
  charge (ordinalRun i xs) ≤ 3*xs.length := ordinalRun_charge

theorem verified_frameFromListRun_value : ∀ {m : ℕ} (V : Square m) (is : List (Fin m)),
  (frameFromListRun V is).value=fun i j => V i (is.get j) := frameFromListRun_value

theorem verified_frameFromListRun_charge : ∀ {m : ℕ} (V : Square m) (is : List (Fin m)),
  charge (frameFromListRun V is)=m*is.length := frameFromListRun_charge

theorem verified_actual_indicator_frame_copy : ∀ {m : ℕ} (V : Square m) (p : Fin m → Prop),
  ((frameFromListRun V (Reference.OrderedIndex.indexList p)).value).submatrix id
      ((finCongr (Reference.OrderedIndex.indexList_length p)).symm)=indicatorFrame V p := actual_indicator_frame_copy

theorem verified_candidateDataRun_charge : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (sigma : Fin m → ℝ) (r : ℕ) (rs : List ℕ)
    (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a),
  charge (candidateDataRun A V sigma r rs) ≤
      9*m+11+m*(1421*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^4) := candidateDataRun_charge

theorem verified_actual_charged_solver_with_genuine_optimum : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hlen : rs.length=ns.length) (hr : 0<r)
    (hns : 0<ns.length) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a),
  feasible m (n::ns) (solverExecutionRun A r rs).value (r::rs) ∧
    0<(candidatesExecutionRun A r rs).value.length ∧
    (candidatesExecutionRun A r rs).value.length≤m ∧
    (0<optimalError A (r::rs) → Reference.OrderedTensorSolver.error A (solverExecutionRun A r rs).value<
      ((ns.length : ℝ)+1)*optimalError A (r::rs)) ∧
    (optimalError A (r::rs)=0 → (solverExecutionRun A r rs).value=A) ∧
    charge (solverExecutionRun A r rs)≤1500*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^5 := actual_charged_solver_with_genuine_optimum

theorem verified_actual_prefix_completion_dense_charge : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (k : ℕ) (rs : List ℕ)
    (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a),
  charge (prefixCompletionRun A V k rs) ≤
      1405*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^4 := actual_prefix_completion_dense_charge

theorem verified_listMapRun_value : ∀ {α β : Type} (f : α → Run β) (xs : List α),
  (listMapRun f xs).value=xs.map (fun x => (f x).value) := listMapRun_value

theorem verified_listMapRun_charge : ∀ {α β : Type} (f : α → Run β) (xs : List α) (C : ℕ)
    (h : ∀ x∈xs,charge (f x)≤C),
  charge (listMapRun f xs)≤xs.length*C := listMapRun_charge

theorem verified_actual_prefix_completion_execution : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (k : ℕ) (rs : List ℕ),
  (prefixCompletionRun A (leftVectorMatrix (denseTensor A)) k rs).value=
      completeFrame A (svdFrame A k) rs := actual_prefix_completion_execution

theorem verified_prefixFrameRun_charge : ∀ {m : ℕ} (V : Square m) (k : ℕ),
  charge (prefixFrameRun V k)=m*min k m := prefixFrameRun_charge

theorem verified_sigmaAtRun_value : ∀ {m : ℕ} (sigma : Fin m → ℝ) (a : ℕ),
  (sigmaAtRun sigma a).value=if h:a<m then sigma ⟨a,h⟩ else 0 := sigmaAtRun_value

theorem verified_sigmaAtRun_charge : ∀ {m : ℕ} (sigma : Fin m → ℝ) (a : ℕ),
  charge (sigmaAtRun sigma a)=3 := sigmaAtRun_charge

theorem verified_actual_tensor_boundary_lookup : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (hrank : r<(denseTensor A).rank),
  (sigmaAtRun (fun i : Fin m => singularValue (denseTensor A).transpose i.val) (r-1)).value=
      tensorBoundary A r := actual_tensor_boundary_lookup

theorem verified_actual_candidate_generator_execution : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hr : 0<r),
  (candidatesExecutionRun A r rs).value=Reference.OrderedTensorSolver.candidates A r rs := actual_candidate_generator_execution

theorem verified_candidateDataRun_count : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (V : Square m) (sigma : Fin m → ℝ) (r : ℕ) (rs : List ℕ)
    (hm : 1≤m),
  0<(candidateDataRun A V sigma r rs).value.length ∧
    (candidateDataRun A V sigma r rs).value.length≤m := candidateDataRun_count

theorem verified_actual_candidate_execution_count : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 1≤m),
  0<(candidatesExecutionRun A r rs).value.length ∧
    (candidatesExecutionRun A r rs).value.length≤m := actual_candidate_execution_count

theorem verified_actual_rank_le_candidate_execution : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hRank : (denseTensor A).rank≤r),
  (candidateDataRun A (leftVectorMatrix (denseTensor A))
      (fun i : Fin m => singularValue (denseTensor A).transpose i.val) r rs).value=
      [Reference.OrderedTensorSolver.columnSpaceCompletion A rs] := actual_rank_le_candidate_execution

theorem verified_actual_full_solver_execution : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hr : 0<r) (hm : 1≤m),
  (solverExecutionRun A r rs).value=Reference.OrderedTensorSolver.solver A r rs := actual_full_solver_execution

theorem verified_equalScanRun_value : ∀ {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ),
  (equalScanRun sigma tau).value=Reference.OrderedIndex.indexList (fun i => sigma i=tau) := equalScanRun_value

theorem verified_aboveScanRun_value : ∀ {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ),
  (aboveScanRun sigma tau).value=Reference.OrderedIndex.indexList (fun i => tau<sigma i) := aboveScanRun_value

theorem verified_equalScanRun_charge : ∀ {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ),
  charge (equalScanRun sigma tau) ≤ 3*m := equalScanRun_charge

theorem verified_aboveScanRun_charge : ∀ {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ),
  charge (aboveScanRun sigma tau) ≤ 3*m := aboveScanRun_charge

theorem verified_windowMaskRun_value : ∀ {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ) (i : Fin m),
  (windowMaskRun sigma tau boundary s j i).value=
      decide (tau<sigma i ∨ sigma i=tau ∧ (boundary.idxOf i+(boundary.length-j))%boundary.length<s) := windowMaskRun_value

theorem verified_windowMaskRun_charge : ∀ {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ) (i : Fin m),
  charge (windowMaskRun sigma tau boundary s j i) ≤ 3*boundary.length+9 := windowMaskRun_charge

theorem verified_windowScanRun_charge : ∀ {m : ℕ} (sigma : Fin m → ℝ) (tau : ℝ)
    (boundary : List (Fin m)) (s j : ℕ),
  charge (windowScanRun sigma tau boundary s j) ≤ m*(3*boundary.length+10) := windowScanRun_charge

theorem verified_actual_spectral_primitive : ∀ {m n : ℕ} (A : Rect m n),
  IsOrthogonal (spectralRun A).value.1 ∧
    (spectralRun A).value.1.transpose*(A*A.transpose)*(spectralRun A).value.1=
      Matrix.diagonal (fun i => ((spectralRun A).value.2 i)^2) ∧
    charge (spectralRun A)=(m+n+1)^3 := actual_spectral_primitive

theorem verified_actual_positive_scan_rank : ∀ {m n : ℕ} (A : Rect m n),
  (aboveScanRun (fun i : Fin m => singularValue A.transpose i.val) 0).value.length=A.rank := actual_positive_scan_rank

theorem verified_actual_candidate_generator_dense_charge : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a),
  charge (candidatesExecutionRun A r rs)≤1470*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^5 := actual_candidate_generator_dense_charge

theorem verified_actual_full_solver_dense_polynomial_charge : ∀ {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (rs : List ℕ) (hm : 1≤m) (hmode : ∀ a∈n::ns,2≤a),
  charge (solverExecutionRun A r rs)≤1500*(Reference.TensorArithmeticExecution.denseSize m (n::ns))^5 := actual_full_solver_dense_polynomial_charge

theorem verified_actual_equal_scan_length : ∀ {m n : ℕ} (A : Rect m n) (tau : ℝ),
  (equalScanRun (sigmaOf A) tau).value.length=eCount A tau := actual_equal_scan_length

theorem verified_actual_above_scan_length : ∀ {m n : ℕ} (A : Rect m n) (tau : ℝ),
  (aboveScanRun (sigmaOf A) tau).value.length=hCount A tau := actual_above_scan_length

theorem verified_actual_window_mask_value : ∀ {m n : ℕ} (A : Rect m n) (tau : ℝ)
    (s : ℕ) (j : Fin (eCount A tau)) (i : Fin m),
  (windowMaskRun (sigmaOf A) tau (equalScanRun (sigmaOf A) tau).value s j.val i).value=
      decide (selected A tau s j i) := actual_window_mask_value

theorem verified_actual_window_scan_value : ∀ {m n : ℕ} (A : Rect m n) (tau : ℝ)
    (s : ℕ) (j : Fin (eCount A tau)),
  (windowScanRun (sigmaOf A) tau (equalScanRun (sigmaOf A) tau).value s j.val).value=
      Reference.OrderedIndex.indexList (selected A tau s j) := actual_window_scan_value

theorem verified_actual_window_scan_charge : ∀ {m n : ℕ} (A : Rect m n) (tau : ℝ)
    (s : ℕ) (j : Fin (eCount A tau)),
  charge (windowScanRun (sigmaOf A) tau (equalScanRun (sigmaOf A) tau).value s j.val) ≤ m*(3*m+10) := actual_window_scan_charge

#print axioms Reference.OrderedTensorExecution.verified_actual_cyclic_execution_charge
#print axioms Reference.OrderedTensorExecution.verified_actual_cyclic_execution_dense_polynomial_charge
#print axioms Reference.OrderedTensorExecution.verified_completeFrame_finCast
#print axioms Reference.OrderedTensorExecution.verified_actual_cyclic_candidate_execution
#print axioms Reference.OrderedTensorExecution.verified_filterRun_value
#print axioms Reference.OrderedTensorExecution.verified_filterRun_charge
#print axioms Reference.OrderedTensorExecution.verified_ordinalRun_value
#print axioms Reference.OrderedTensorExecution.verified_ordinalRun_charge
#print axioms Reference.OrderedTensorExecution.verified_frameFromListRun_value
#print axioms Reference.OrderedTensorExecution.verified_frameFromListRun_charge
#print axioms Reference.OrderedTensorExecution.verified_actual_indicator_frame_copy
#print axioms Reference.OrderedTensorExecution.verified_candidateDataRun_charge
#print axioms Reference.OrderedTensorExecution.verified_actual_charged_solver_with_genuine_optimum
#print axioms Reference.OrderedTensorExecution.verified_actual_prefix_completion_dense_charge
#print axioms Reference.OrderedTensorExecution.verified_listMapRun_value
#print axioms Reference.OrderedTensorExecution.verified_listMapRun_charge
#print axioms Reference.OrderedTensorExecution.verified_actual_prefix_completion_execution
#print axioms Reference.OrderedTensorExecution.verified_prefixFrameRun_charge
#print axioms Reference.OrderedTensorExecution.verified_sigmaAtRun_value
#print axioms Reference.OrderedTensorExecution.verified_sigmaAtRun_charge
#print axioms Reference.OrderedTensorExecution.verified_actual_tensor_boundary_lookup
#print axioms Reference.OrderedTensorExecution.verified_actual_candidate_generator_execution
#print axioms Reference.OrderedTensorExecution.verified_candidateDataRun_count
#print axioms Reference.OrderedTensorExecution.verified_actual_candidate_execution_count
#print axioms Reference.OrderedTensorExecution.verified_actual_rank_le_candidate_execution
#print axioms Reference.OrderedTensorExecution.verified_actual_full_solver_execution
#print axioms Reference.OrderedTensorExecution.verified_equalScanRun_value
#print axioms Reference.OrderedTensorExecution.verified_aboveScanRun_value
#print axioms Reference.OrderedTensorExecution.verified_equalScanRun_charge
#print axioms Reference.OrderedTensorExecution.verified_aboveScanRun_charge
#print axioms Reference.OrderedTensorExecution.verified_windowMaskRun_value
#print axioms Reference.OrderedTensorExecution.verified_windowMaskRun_charge
#print axioms Reference.OrderedTensorExecution.verified_windowScanRun_charge
#print axioms Reference.OrderedTensorExecution.verified_actual_spectral_primitive
#print axioms Reference.OrderedTensorExecution.verified_actual_positive_scan_rank
#print axioms Reference.OrderedTensorExecution.verified_actual_candidate_generator_dense_charge
#print axioms Reference.OrderedTensorExecution.verified_actual_full_solver_dense_polynomial_charge
#print axioms Reference.OrderedTensorExecution.verified_actual_equal_scan_length
#print axioms Reference.OrderedTensorExecution.verified_actual_above_scan_length
#print axioms Reference.OrderedTensorExecution.verified_actual_window_mask_value
#print axioms Reference.OrderedTensorExecution.verified_actual_window_scan_value
#print axioms Reference.OrderedTensorExecution.verified_actual_window_scan_charge
end Reference.OrderedTensorExecution
end
