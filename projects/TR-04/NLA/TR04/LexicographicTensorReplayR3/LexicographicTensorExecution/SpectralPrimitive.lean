module

public import NLA.TR04.LexicographicTensorReplayR3.PureDefinitions
/- Validity of the fixed exact spectral primitive and actual rank from finite scans. -/
public import NLA.TR04.LexicographicTensorReplayR3.LexicographicTensorExecution.ScanChecks
public import NLA.TR04.OptimalityEquality.Boundary
public import NLA.TR04.OptimalityEquality.ActualBasis
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.LexTensorExecution
noncomputable section
attribute [local instance] Classical.propDecidable
open Reference.RealSVDPackage Reference.RealOptimalityEquality
open scoped Matrix

theorem actual_spectral_primitive {m n : ℕ} (A : Rect m n) :
    IsOrthogonal (spectralRun A).value.1 ∧
    (spectralRun A).value.1.transpose*(A*A.transpose)*(spectralRun A).value.1=
      Matrix.diagonal (fun i => ((spectralRun A).value.2 i)^2) ∧
    charge (spectralRun A)=(m+n+1)^3 := by
  exact ⟨leftVectorMatrix_orthogonal A,leftVectorMatrix_gram_diagonal A,rfl⟩

theorem actual_positive_scan_rank {m n : ℕ} (A : Rect m n) :
    (aboveScanRun (fun i : Fin m => singularValue A.transpose i.val) 0).value.length=A.rank := by
  rw [aboveScanRun_value,Reference.LexOrderedIndex.indexList_length]
  simpa only [Fintype.card_fin] using Fintype.card_congr (positiveRankEquiv A)

#print axioms actual_spectral_primitive
#print axioms actual_positive_scan_rank
end
end Reference.LexTensorExecution
