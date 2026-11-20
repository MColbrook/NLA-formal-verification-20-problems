module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Concrete finite grouped-unfolding bridge for TR04, extending the checked real
MI-13/RA02 matrix and column-compression infrastructure. MI-13 source commit
 e375a6fc0a12df52c4f5a38b53df78b837e1c390. Prior mathematical attribution
retained; new finite regrouping formalization by Codex, 2026-10-03.
No unfolding-rank, spectral, runtime or tensor-correctness contract is assumed.
-/
public import NLA.TR04.RealSVD.Compression
public import NLA.TR04.TensorGroupingDefinitions
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorGrouping
noncomputable section
open Reference.RealSVDPackage
open Reference.RealColumnCompression
open scoped BigOperators Matrix Kronecker

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [Fintype κ] in
theorem grouped_mul {m k : ℕ} (U : Rect m k) (C : Matrix (Fin k) (ι × κ) ℝ) :
    grouped (U * C) = (U ⊗ₖ (1 : Matrix ι ι ℝ)) * grouped C := by
  classical
  ext p j
  rcases p with ⟨i, g⟩
  simp [grouped, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]

omit [Fintype κ] in
theorem grouped_compression {m k : ℕ} (U : Rect m k)
    (A : Matrix (Fin m) (ι × κ) ℝ) :
    grouped (U.transpose * A) =
      (U.transpose ⊗ₖ (1 : Matrix ι ι ℝ)) * grouped A :=
  grouped_mul U.transpose A

theorem grouped_compression_rank_le {m k : ℕ} (U : Rect m k)
    (A : Matrix (Fin m) (ι × κ) ℝ) :
    (grouped (U.transpose * A)).rank ≤ (grouped A).rank := by
  rw [grouped_compression]
  exact Matrix.rank_mul_le_right _ _

theorem grouped_lifting_rank_le {m k : ℕ} (U : Rect m k)
    (C : Matrix (Fin k) (ι × κ) ℝ) :
    (grouped (U * C)).rank ≤ (grouped C).rank := by
  rw [grouped_mul]
  exact Matrix.rank_mul_le_right _ _

theorem grouped_lifting_rank_eq {m k : ℕ} (U : Rect m k)
    (hU : U.transpose * U = 1) (C : Matrix (Fin k) (ι × κ) ℝ) :
    (grouped (U * C)).rank = (grouped C).rank := by
  apply le_antisymm (grouped_lifting_rank_le U C)
  have hback : U.transpose * (U * C) = C := by
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  have hb := grouped_compression_rank_le U (U * C)
  rw [hback] at hb
  exact hb

omit [DecidableEq ι] in
theorem grouped_frobeniusSq {m : ℕ} (A : Matrix (Fin m) (ι × κ) ℝ) :
    entryFrobeniusSq (grouped A) = entryFrobeniusSq A := by
  simp only [entryFrobeniusSq, grouped, Fintype.sum_prod_type]

theorem entryFrobeniusSq_reindex_columns {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] (e : β ≃ γ) (A : Matrix α β ℝ) :
    entryFrobeniusSq (A.submatrix id e.symm) = entryFrobeniusSq A := by
  simp only [entryFrobeniusSq, Matrix.submatrix_apply, id_eq]
  apply Finset.sum_congr rfl
  intro i _
  exact e.symm.sum_comp (fun j => A i j ^ 2)

theorem finite_column_compression_frobenius_le {β : Type*} [Fintype β]
    {m k : ℕ} (U : Rect m k) (hU : U.transpose * U = 1)
    (A : Matrix (Fin m) β ℝ) :
    entryFrobeniusSq (U.transpose * A) ≤ entryFrobeniusSq A := by
  classical
  let e := Fintype.equivFin β
  let A' : Rect m (Fintype.card β) := A.submatrix id e.symm
  have hd := orthonormal_column_error_decomposition U hU A'
    (0 : Rect k (Fintype.card β))
  simp only [Matrix.mul_zero, sub_zero] at hd
  have hn := frobeniusSq_nonneg (A' - U * U.transpose * A')
  have hb : frobeniusSq (U.transpose * A') ≤ frobeniusSq A' := by linarith
  change entryFrobeniusSq (U.transpose * A') ≤ entryFrobeniusSq A' at hb
  have he : U.transpose * A' = (U.transpose * A).submatrix id e.symm := by
    ext i j
    rfl
  rw [he, entryFrobeniusSq_reindex_columns, entryFrobeniusSq_reindex_columns] at hb
  exact hb

theorem finite_column_lifting_frobenius_eq {β : Type*} [Fintype β]
    {m k : ℕ} (U : Rect m k) (hU : U.transpose * U = 1)
    (C : Matrix (Fin k) β ℝ) :
    entryFrobeniusSq (U * C) = entryFrobeniusSq C := by
  classical
  let e := Fintype.equivFin β
  let C' : Rect k (Fintype.card β) := C.submatrix id e.symm
  have hb := frobeniusSq_frame_mul U hU C'
  change entryFrobeniusSq (U * C') = entryFrobeniusSq C' at hb
  have he : U * C' = (U * C).submatrix id e.symm := by
    ext i j
    rfl
  rw [he, entryFrobeniusSq_reindex_columns, entryFrobeniusSq_reindex_columns] at hb
  exact hb

omit [DecidableEq ι] in
theorem grouped_compression_frobenius_le {m k : ℕ} (U : Rect m k)
    (hU : U.transpose * U = 1) (A : Matrix (Fin m) (ι × κ) ℝ) :
    entryFrobeniusSq (grouped (U.transpose * A)) ≤ entryFrobeniusSq (grouped A) := by
  rw [grouped_frobeniusSq, grouped_frobeniusSq]
  exact finite_column_compression_frobenius_le U hU A

omit [DecidableEq ι] in
theorem grouped_lifting_frobenius_eq {m k : ℕ} (U : Rect m k)
    (hU : U.transpose * U = 1) (C : Matrix (Fin k) (ι × κ) ℝ) :
    entryFrobeniusSq (grouped (U * C)) = entryFrobeniusSq (grouped C) := by
  rw [grouped_frobeniusSq, grouped_frobeniusSq]
  exact finite_column_lifting_frobenius_eq U hU C

#print axioms grouped_mul
#print axioms grouped_compression
#print axioms grouped_compression_rank_le
#print axioms grouped_lifting_rank_le
#print axioms grouped_lifting_rank_eq
#print axioms grouped_frobeniusSq
#print axioms grouped_compression_frobenius_le
#print axioms grouped_lifting_frobenius_eq
end
end Reference.TensorGrouping

