module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Real prefix-column frame extension of the checked MI-13/RA02 adaptations.
Upstream MI-13 commit e375a6fc0a12df52c4f5a38b53df78b837e1c390.
Accepted RA02 variational attribution retained. Adapted by Codex, 2026-10-03.
No frozen package source is modified or spectral/runtime contract supplied. -/
public import NLA.TR04.RealSVD.Compression

@[expose] public section

set_option autoImplicit false
namespace Reference.RealColumnCompression
noncomputable section
open Reference.RealSVDPackage
open scoped BigOperators Matrix

def headIndex (m r : ℕ) (j : Fin (min r m)) : Fin m :=
  ⟨j.val, j.isLt.trans_le (Nat.min_le_right r m)⟩

theorem headIndex_injective (m r : ℕ) : Function.Injective (headIndex m r) := by
  intro j l h
  apply Fin.ext
  exact congrArg (fun x : Fin m => x.val) h

def firstColumns {m : ℕ} (V : Square m) (r : ℕ) : Rect m (min r m) :=
  fun i j => V i (headIndex m r j)

theorem headIndex_sum (m r : ℕ) (f : Fin m → ℝ) :
    (∑ j : Fin (min r m), f (headIndex m r j)) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin m => i.val < r), f i := by
  classical
  apply Finset.sum_bij (fun j _ => headIndex m r j)
  · intro j _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact j.isLt.trans_le (Nat.min_le_left r m)
  · intro j _ l _ h
    exact headIndex_injective m r h
  · intro i hi
    refine ⟨⟨i.val, Nat.lt_min.mpr ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩⟩,
      Finset.mem_univ _, ?_⟩
    apply Fin.ext
    rfl
  · intro j _
    rfl

theorem firstColumns_orthonormal {m : ℕ} (V : Square m)
    (hV : IsOrthogonal V) (r : ℕ) :
    (firstColumns V r).transpose * firstColumns V r = 1 := by
  classical
  ext j l
  have h := congrArg (fun M : Square m => M (headIndex m r j) (headIndex m r l)) hV.1
  change (∑ i, V i (headIndex m r j) * V i (headIndex m r l)) = _ at h
  change (∑ i, V i (headIndex m r j) * V i (headIndex m r l)) =
    (1 : Square (min r m)) j l
  simpa only [Matrix.one_apply, (headIndex_injective m r).eq_iff] using h

theorem firstColumns_projection {m : ℕ} (V : Square m) (r : ℕ) :
    firstColumns V r * (firstColumns V r).transpose =
      V * Matrix.diagonal (headMask m r) * V.transpose := by
  classical
  ext i l
  change (∑ j : Fin (min r m), V i (headIndex m r j) * V l (headIndex m r j)) = _
  rw [headIndex_sum m r (fun j => V i j * V l j), Finset.sum_filter,
    Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, headMask]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < r <;> simp [hj]

theorem exists_exact_column_projection {m n : ℕ} (A : Rect m n) (r : ℕ) :
    ∃ U : Rect m (min r m), U.transpose * U = 1 ∧
      (U * U.transpose * A).rank ≤ r ∧
      frobeniusSq (A - U * U.transpose * A) = singularTailSq A r := by
  obtain ⟨V, hV, hdiag⟩ := rectangular_right_gram_diagonal A.transpose
  let U := firstColumns V r
  have hU : U.transpose * U = 1 := firstColumns_orthonormal V hV r
  have hp : U * U.transpose * A = (realTruncation A.transpose r V).transpose := by
    dsimp [U]
    rw [firstColumns_projection]
    simp only [realTruncation, Matrix.transpose_mul, Matrix.diagonal_transpose,
      Matrix.transpose_transpose, Matrix.mul_assoc]
  refine ⟨U, hU, ?_, ?_⟩
  · rw [hp, Matrix.rank_transpose]
    exact realTruncation_rank_le A.transpose r V
  · calc
      frobeniusSq (A - U * U.transpose * A) =
          frobeniusSq (A.transpose - realTruncation A.transpose r V) := by
        rw [hp]
        simpa only [Matrix.transpose_sub, Matrix.transpose_transpose] using
          frobeniusSq_transpose (A.transpose - realTruncation A.transpose r V)
      _ = singularTailSq A.transpose r := realTruncation_error A.transpose r V hV hdiag
      _ = singularTailSq A r := singularTailSq_transpose A r

#print axioms firstColumns_orthonormal
#print axioms firstColumns_projection
#print axioms exists_exact_column_projection
end
end Reference.RealColumnCompression


