module

/- Copyright (c) 2026 George Stepaniants. Released under Apache 2.0 license.
Real orthonormal-column compression extension of the checked MI-13/RA02
adaptations. Upstream MI-13 commit e375a6fc0a12df52c4f5a38b53df78b837e1c390.
Original accepted RA02 variational attribution retained; adapted by Codex,
2026-10-03. Reference-only extension; frozen package sources unchanged. -/
public import NLA.TR04.RealSVD.RealLower

@[expose] public section

set_option autoImplicit false
namespace Reference.RealColumnCompression
noncomputable section
open Reference.RealSVDPackage
open scoped BigOperators Matrix

theorem frobeniusSq_transpose {m n : ℕ} (A : Rect m n) :
    frobeniusSq A.transpose = frobeniusSq A := by
  simp only [frobeniusSq, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem frobeniusSq_frame_mul {m k n : ℕ} (U : Rect m k)
    (hU : U.transpose * U = 1) (X : Rect k n) :
    frobeniusSq (U * X) = frobeniusSq X := by
  rw [frobeniusSq_eq_gram_trace, frobeniusSq_eq_gram_trace, Matrix.transpose_mul]
  calc
    _ = (X.transpose * (U.transpose * U) * X).trace := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, Matrix.mul_one]

theorem frobeniusSq_add_of_gram_zero {m n : ℕ} (E D : Rect m n)
    (hED : E.transpose * D = 0) :
    frobeniusSq (E + D) = frobeniusSq E + frobeniusSq D := by
  have hDE : D.transpose * E = 0 := by
    have ht := congrArg Matrix.transpose hED
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] using ht
  rw [frobeniusSq_eq_gram_trace, frobeniusSq_eq_gram_trace,
    frobeniusSq_eq_gram_trace]
  simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add,
    Matrix.trace_add, hED, hDE, add_zero, zero_add]

theorem orthonormal_column_error_decomposition {m k n : ℕ}
    (U : Rect m k) (hU : U.transpose * U = 1) (A : Rect m n) (C : Rect k n) :
    frobeniusSq (A - U * C) = frobeniusSq (A - U * U.transpose * A) +
      frobeniusSq (U.transpose * A - C) := by
  let E := A - U * U.transpose * A
  let X := U.transpose * A - C
  have hUE : U.transpose * E = 0 := by
    dsimp [E]
    rw [Matrix.mul_sub]
    have he : U.transpose * (U * U.transpose * A) = U.transpose * A := by
      calc
        _ = (U.transpose * U) * (U.transpose * A) := by
          simp only [Matrix.mul_assoc]
        _ = _ := by rw [hU, Matrix.one_mul]
    rw [he, sub_self]
  have hEU : E.transpose * U = 0 := by
    have ht := congrArg Matrix.transpose hUE
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_zero] using ht
  have hcross : E.transpose * (U * X) = 0 := by
    rw [← Matrix.mul_assoc, hEU, Matrix.zero_mul]
  have hsplit : A - U * C = E + U * X := by
    dsimp [E, X]
    rw [Matrix.mul_sub]
    simp only [← Matrix.mul_assoc]
    abel
  rw [hsplit, frobeniusSq_add_of_gram_zero E (U * X) hcross,
    frobeniusSq_frame_mul U hU X]

theorem singularTailSq_transpose {m n : ℕ} (A : Rect m n) (r : ℕ) :
    singularTailSq A.transpose r = singularTailSq A r := by
  apply le_antisymm
  · obtain ⟨B, hB, he⟩ := real_rank_r_frobenius_attainment A r
    have hl := singularTail_le_lowRankError A.transpose B.transpose r
      (by rw [Matrix.rank_transpose]; exact hB)
    simpa only [← Matrix.transpose_sub, frobeniusSq_transpose, he] using hl
  · obtain ⟨B, hB, he⟩ := real_rank_r_frobenius_attainment A.transpose r
    have hl := singularTail_le_lowRankError A B.transpose r
      (by rw [Matrix.rank_transpose]; exact hB)
    have hf : frobeniusSq (A - B.transpose) = frobeniusSq (A.transpose - B) := by
      rw [← frobeniusSq_transpose (A.transpose - B)]
      simp only [Matrix.transpose_sub, Matrix.transpose_transpose]
    rw [hf, he] at hl
    exact hl

#print axioms orthonormal_column_error_decomposition
#print axioms singularTailSq_transpose
end
end Reference.RealColumnCompression

