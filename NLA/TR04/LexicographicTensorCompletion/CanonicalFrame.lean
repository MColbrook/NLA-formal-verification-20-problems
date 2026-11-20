module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
The named TT-SVD primitive frame has actual orthonormality and optimal projection error.
Correctness derives from the ACTUAL sorted Gram basis/truncation, not an oracle.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.LexicographicTensorCompletion.ProcessDefinitions
public import NLA.TR04.LexicographicTensorCompletion.Projection
public import NLA.TR04.OptimalityEquality.ActualBasis

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage Reference.RealColumnCompression Reference.RealOptimalityEquality Reference.TensorGrouping
open scoped Matrix

theorem svdFrame_correct {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) :
    (svdFrame A r).transpose*svdFrame A r=1 ∧
      ∀ Y : Tensor m ns, Y.rank ≤ r →
        tensorFrobeniusSq (A-svdFrame A r*(svdFrame A r).transpose*A) ≤ tensorFrobeniusSq (A-Y) := by
  classical
  let A' := denseTensor A
  let V := leftVectorMatrix A'
  let U := svdFrame A r
  have hUDef : U=firstColumns V r := rfl
  have hV : IsOrthogonal V := leftVectorMatrix_orthogonal A'
  have hdiag : V.transpose*(A'*A'.transpose)*V =
      Matrix.diagonal (fun i : Fin m => singularValue A'.transpose i.val^2) :=
    leftVectorMatrix_gram_diagonal A'
  have hU : U.transpose*U=1 := by rw [hUDef];exact firstColumns_orthonormal V hV r
  have hp : U*U.transpose*A'=(realTruncation A'.transpose r V).transpose := by
    rw [hUDef,firstColumns_projection]
    simp only [realTruncation,Matrix.transpose_mul,Matrix.diagonal_transpose,
      Matrix.transpose_transpose,Matrix.mul_assoc]
  have he : frobeniusSq (A'-U*U.transpose*A')=singularTailSq A' r := by
    calc
      _ = frobeniusSq (A'.transpose-realTruncation A'.transpose r V) := by
        rw [hp]
        simpa only [Matrix.transpose_sub,Matrix.transpose_transpose] using
          frobeniusSq_transpose (A'.transpose-realTruncation A'.transpose r V)
      _ = singularTailSq A'.transpose r := realTruncation_error A'.transpose r V hV
        (by simpa only [Matrix.transpose_transpose] using hdiag)
      _ = _ := singularTailSq_transpose A' r
  refine ⟨hU,?_⟩
  intro Y hY
  let e := concreteLayout ns
  let Y' : Rect m (Fintype.card (ModeIndex ns)) := Y.submatrix id e.symm
  have hlo := singularTail_le_lowRankError A' Y' r
    ((Matrix.rank_submatrix_le Y id e.symm).trans hY)
  have ha : A'-U*U.transpose*A'=(A-U*U.transpose*A).submatrix id e.symm := rfl
  have hb : A'-Y'=(A-Y).submatrix id e.symm := rfl
  change entryFrobeniusSq (A-U*U.transpose*A) ≤ entryFrobeniusSq (A-Y)
  calc
    _ = frobeniusSq (A'-U*U.transpose*A') := by
      change _ = entryFrobeniusSq (A'-U*U.transpose*A')
      rw [ha,entryFrobeniusSq_reindex_columns]
    _ = singularTailSq A' r := he
    _ ≤ frobeniusSq (A'-Y') := hlo
    _ = _ := by
      change entryFrobeniusSq (A'-Y') = _
      rw [hb,entryFrobeniusSq_reindex_columns]

#print axioms svdFrame_correct
end
end Reference.LexTensorCompletion
