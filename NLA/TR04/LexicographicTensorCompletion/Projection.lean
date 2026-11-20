module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Actual optimal first-cut column projection for any finite nested tensor shape.
The frame comes from proved real Gram/SVD attainment, not a supplied oracle.
New reference-only proof by Codex, 2026-10-03. -/
public import NLA.TR04.LexicographicTensorCompletion.RankPreservation
public import NLA.TR04.RealSVD.ColumnFrame

@[expose] public section

set_option autoImplicit false
namespace Reference.LexTensorCompletion
noncomputable section
open Reference.RealSVDPackage Reference.RealColumnCompression Reference.TensorGrouping

theorem exists_actual_first_projection {m : ℕ} {ns : List ℕ} (A : Tensor m ns) (r : ℕ) :
    ∃ U : Rect m (min r m), U.transpose*U=1 ∧
      ∀ Y : Tensor m ns, Y.rank ≤ r →
        tensorFrobeniusSq (A-U*U.transpose*A) ≤ tensorFrobeniusSq (A-Y) := by
  classical
  let e := Fintype.equivFin (ModeIndex ns)
  let A' : Rect m (Fintype.card (ModeIndex ns)) := A.submatrix id e.symm
  obtain ⟨U,hU,hRank,hErr⟩ := exists_exact_column_projection A' r
  refine ⟨U,hU,?_⟩
  intro Y hY
  let Y' : Rect m (Fintype.card (ModeIndex ns)) := Y.submatrix id e.symm
  have hY' : Y'.rank ≤ r := (Matrix.rank_submatrix_le Y id e.symm).trans hY
  have hlo := singularTail_le_lowRankError A' Y' r hY'
  have ha : A'-U*U.transpose*A' = (A-U*U.transpose*A).submatrix id e.symm := rfl
  have hb : A'-Y' = (A-Y).submatrix id e.symm := rfl
  change entryFrobeniusSq (A-U*U.transpose*A) ≤ entryFrobeniusSq (A-Y)
  calc
    _ = frobeniusSq (A'-U*U.transpose*A') := by
      change _ = entryFrobeniusSq (A'-U*U.transpose*A')
      rw [ha,entryFrobeniusSq_reindex_columns]
    _ = singularTailSq A' r := hErr
    _ ≤ frobeniusSq (A'-Y') := hlo
    _ = _ := by
      change entryFrobeniusSq (A'-Y') = _
      rw [hb,entryFrobeniusSq_reindex_columns]

theorem tensor_column_error_decomposition {m k : ℕ} {ns : List ℕ}
    (U : Rect m k) (hU : U.transpose*U=1) (A : Tensor m ns) (C : Tensor k ns) :
    tensorFrobeniusSq (A-U*C) = tensorFrobeniusSq (A-U*U.transpose*A) +
      tensorFrobeniusSq (U.transpose*A-C) :=
  Reference.ThreeModeCompletion.finite_orthonormal_column_error_decomposition U hU A C

theorem tensor_compression_frobenius_le {m k : ℕ} {ns : List ℕ}
    (U : Rect m k) (hU : U.transpose*U=1) (A : Tensor m ns) :
    tensorFrobeniusSq (U.transpose*A) ≤ tensorFrobeniusSq A :=
  finite_column_compression_frobenius_le U hU A

theorem tensor_lifting_frobenius_eq {m k : ℕ} {ns : List ℕ}
    (U : Rect m k) (hU : U.transpose*U=1) (A : Tensor k ns) :
    tensorFrobeniusSq (U*A) = tensorFrobeniusSq A :=
  finite_column_lifting_frobenius_eq U hU A

#print axioms exists_actual_first_projection
#print axioms tensor_column_error_decomposition
end
end Reference.LexTensorCompletion
