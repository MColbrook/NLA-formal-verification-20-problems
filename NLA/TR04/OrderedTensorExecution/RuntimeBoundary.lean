module

/- Provenance of runtime first-cut rank and boundary values from the spectral reply. -/
public import NLA.TR04.OrderedTensorExecution.ProgramLoops
public import NLA.TR04.OrderedTensorExecution.SpectralPrimitive
public import NLA.TR04.OrderedTensorSolver.Candidates
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.OrderedTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.RecursiveTensorCompletion Reference.OrderedCyclicBoundary

theorem actual_tensor_boundary_lookup {m n : ℕ} {ns : List ℕ}
    (A : Tensor m (n::ns)) (r : ℕ) (hrank : r<(denseTensor A).rank) :
    (sigmaAtRun (fun i : Fin m => singularValue (denseTensor A).transpose i.val) (r-1)).value=
      tensorBoundary A r := by
  have hbound := Matrix.rank_le_width (denseTensor A).transpose
  rw [Matrix.rank_transpose] at hbound
  have hi : r-1<m := by omega
  rw [sigmaAtRun_value,dif_pos hi]
  exact singularValue_transpose (denseTensor A) (r-1)

#print axioms actual_tensor_boundary_lookup
end
end Reference.OrderedTensorExecution
