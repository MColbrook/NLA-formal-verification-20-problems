module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Provenance of runtime first-cut rank and boundary values from the spectral reply. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.ProgramLoops
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.SpectralPrimitive
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorSolver.Candidates
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexTensorExecution
noncomputable section
open Reference.RealSVDPackage Reference.RealOptimalityEquality Reference.LexTensorCompletion Reference.LexOrderedCyclicBoundary

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
end Reference.LexTensorExecution
