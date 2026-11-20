module

/- Validity of the fixed exact spectral primitive and actual rank from finite scans. -/
public import NLA.TR04.OrderedTensorExecution.ScanChecks
public import NLA.TR04.OptimalityEquality.Boundary
public import NLA.TR04.OptimalityEquality.ActualBasis
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Reference.OrderedTensorExecution
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

def positiveRankEquiv {m n : ℕ} (A : Rect m n) :
    {i : Fin m // 0<singularValue A.transpose i.val} ≃ Fin A.rank where
  toFun i := ⟨i.val.val,by
    have h := (singularValue_pos_iff_lt_rank A.transpose i.val.val).mp i.property
    simpa only [Matrix.rank_transpose] using h⟩
  invFun j := ⟨⟨j.val,by
      have h := Matrix.rank_le_width A.transpose
      rw [Matrix.rank_transpose] at h
      exact lt_of_lt_of_le j.isLt h⟩,by
    apply (singularValue_pos_iff_lt_rank A.transpose j.val).mpr
    simpa only [Matrix.rank_transpose] using j.isLt⟩
  left_inv i := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv j := by apply Fin.ext; rfl

theorem actual_positive_scan_rank {m n : ℕ} (A : Rect m n) :
    (aboveScanRun (fun i : Fin m => singularValue A.transpose i.val) 0).value.length=A.rank := by
  rw [aboveScanRun_value,Reference.OrderedIndex.indexList_length]
  simpa only [Fintype.card_fin] using Fintype.card_congr (positiveRankEquiv A)

#print axioms actual_spectral_primitive
#print axioms actual_positive_scan_rank
end
end Reference.OrderedTensorExecution
