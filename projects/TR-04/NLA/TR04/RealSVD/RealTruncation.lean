module

/-
Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Department of Computing and Mathematical Sciences, California Institute of Technology.
Substantial OpenAI Codex assistance. Prior mathematical attribution is retained.

Real rectangular head-mask adaptation of the accepted RA-02 construction,
using the real right Gram basis adapted from OpenProblemsInNLA MI-13 at commit
e375a6fc0a12df52c4f5a38b53df78b837e1c390. Adapted by Codex, 2026-10-03.
This module proves the actual rank and attained singular-tail error only;
it does not assert optimality against all competitors or a running-time bound.
-/
public import NLA.TR04.RealSVD.RectangularGram
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.Trace

@[expose] public section

set_option autoImplicit false

namespace Reference.RealSVDPackage
noncomputable section
open scoped BigOperators Matrix

theorem frobeniusSq_nonneg {m n : ℕ} (E : Rect m n) : 0 ≤ frobeniusSq E := by
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (E i j)))

theorem frobeniusSq_eq_gram_trace {m n : ℕ} (E : Rect m n) :
    frobeniusSq E = Matrix.trace (E.transpose * E) := by
  simp only [frobeniusSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

theorem frobeniusSq_orthogonal_right {m n : ℕ} (E : Rect m n)
    (V : Square n) (hV : IsOrthogonal V) : frobeniusSq (E * V) = frobeniusSq E := by
  rw [frobeniusSq_eq_gram_trace, frobeniusSq_eq_gram_trace]
  have he : (E * V).transpose * (E * V) =
      V.transpose * (E.transpose * E) * V := by
    simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [he, Matrix.trace_mul_cycle, hV.2, Matrix.one_mul]

theorem transpose_orthogonal {n : ℕ} (V : Square n) (hV : IsOrthogonal V) :
    IsOrthogonal V.transpose := by
  exact ⟨by simpa only [Matrix.transpose_transpose] using hV.2,
    by simpa only [Matrix.transpose_transpose] using hV.1⟩

theorem headMask_rank_le (n r : ℕ) : (Matrix.diagonal (headMask n r)).rank ≤ r := by
  classical
  rw [Matrix.rank_diagonal]
  let f : {i : Fin n // headMask n r i ≠ 0} → Fin r := fun i =>
    ⟨i.val.val, by simpa [headMask] using i.property⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun x : Fin r => x.val) hij
  exact (Fintype.card_le_of_injective f hf).trans_eq (Fintype.card_fin r)

theorem realTruncation_rank_le {m n : ℕ} (A : Rect m n) (r : ℕ) (V : Square n) :
    (realTruncation A r V).rank ≤ r := by
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans (headMask_rank_le n r))

theorem head_tail_diagonal (n r : ℕ) :
    (1 : Square n) - Matrix.diagonal (headMask n r) =
      Matrix.diagonal (tailMask n r) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i.val < r <;>
      simp [headMask, tailMask, hi]
  · simp [hij]

theorem realTruncation_residual {m n : ℕ} (A : Rect m n) (r : ℕ)
    (V : Square n) (hV : IsOrthogonal V) :
    A - realTruncation A r V = A * V * Matrix.diagonal (tailMask n r) * V.transpose := by
  have hA : A = A * V * (1 : Square n) * V.transpose := by
    rw [Matrix.mul_one, Matrix.mul_assoc, hV.2, Matrix.mul_one]
  change A - A * V * Matrix.diagonal (headMask n r) * V.transpose = _
  conv_lhs => lhs; rw [hA]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, head_tail_diagonal]

theorem realTruncation_error {m n : ℕ} (A : Rect m n) (r : ℕ)
    (V : Square n) (hV : IsOrthogonal V)
    (hdiag : V.transpose * (A.transpose * A) * V =
      Matrix.diagonal (fun i : Fin n => singularValue A i.val ^ 2)) :
    frobeniusSq (A - realTruncation A r V) = singularTailSq A r := by
  classical
  rw [realTruncation_residual A r V hV]
  rw [frobeniusSq_orthogonal_right _ V.transpose (transpose_orthogonal V hV),
    frobeniusSq_eq_gram_trace]
  have hg : (A * V * Matrix.diagonal (tailMask n r)).transpose *
        (A * V * Matrix.diagonal (tailMask n r)) =
      Matrix.diagonal (tailMask n r) *
        (V.transpose * (A.transpose * A) * V) * Matrix.diagonal (tailMask n r) := by
    simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
  rw [hg, hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  change (∑ i : Fin n, tailMask n r i * (singularValue A i.val ^ 2) * tailMask n r i) =
    ∑ i ∈ Finset.univ.filter (fun i : Fin n => r ≤ i.val), singularValue A i.val ^ 2
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < r
  · simp [tailMask, hi, show ¬ r ≤ i.val from by omega]
  · simp [tailMask, hi, show r ≤ i.val from by omega]

theorem real_rank_r_mask_attainment {m n : ℕ} (A : Rect m n) (r : ℕ) :
    ∃ V : Square n, IsOrthogonal V ∧ (realTruncation A r V).rank ≤ r ∧
      frobeniusSq (A - realTruncation A r V) = singularTailSq A r := by
  obtain ⟨V, hV, hdiag⟩ := rectangular_right_gram_diagonal A
  exact ⟨V, hV, realTruncation_rank_le A r V, realTruncation_error A r V hV hdiag⟩

theorem real_rank_r_frobenius_attainment {m n : ℕ} (A : Rect m n) (r : ℕ) :
    ∃ B : Rect m n, B.rank ≤ r ∧ frobeniusSq (A - B) = singularTailSq A r := by
  obtain ⟨V, _, hRank, hError⟩ := real_rank_r_mask_attainment A r
  exact ⟨realTruncation A r V, hRank, hError⟩

#print axioms frobeniusSq_eq_gram_trace
#print axioms frobeniusSq_orthogonal_right
#print axioms headMask_rank_le
#print axioms realTruncation_rank_le
#print axioms realTruncation_residual
#print axioms realTruncation_error
#print axioms real_rank_r_mask_attainment
#print axioms real_rank_r_frobenius_attainment

end
end Reference.RealSVDPackage

