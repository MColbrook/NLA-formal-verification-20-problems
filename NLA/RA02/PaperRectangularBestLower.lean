module

public import NLA.RA02.PaperRectangularBestDefinitions
public import NLA.RA02.PaperKernelFrame
public import NLA.RA02.PaperLUUpper

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem gramTail_le_lowRankError {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℂ)
    (r : ℕ) (hB : B.rank ≤ r) : gramTail A r ≤ NLA.RA03.frobeniusSq (A-B) := by
  obtain ⟨q,U,hdim,hU,hBU⟩ := exists_kernel_frame B r hB
  have hEU : (A-B)*U = A*U := by rw [Matrix.sub_mul,hBU,sub_zero]
  have he : U.conjTranspose*(A.conjTranspose*A)*U =
      U.conjTranspose*((A-B).conjTranspose*(A-B))*U := by
    calc
      _ = (A*U).conjTranspose*(A*U) := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
      _ = ((A-B)*U).conjTranspose*((A-B)*U) := by rw [hEU]
      _ = _ := by simp only [Matrix.conjTranspose_mul,Matrix.mul_assoc]
  have hb := rankTail_le_compression_trace (A.conjTranspose*A) (Matrix.posSemidef_conjTranspose_mul_self A) r hdim U hU
  rw [he] at hb
  exact hb.trans (frobenius_compression_bound (A-B) U hU)

theorem gramTail_le_rectangularBest {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) :
    gramTail A r ≤ rectangularBestRankErrorSquared A r := by
  apply le_csInf
  · refine ⟨NLA.RA03.frobeniusSq A,0,?_,?_⟩
    · simp only [Matrix.rank_zero]; exact Nat.zero_le r
    · simp only [sub_zero]
  · rintro e ⟨B,hB,he⟩
    rw [← he]
    exact gramTail_le_lowRankError A B r hB

theorem rectangularBest_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ) :
    0 ≤ rectangularBestRankErrorSquared A r :=
  (NLA.RA02.rankTail_nonneg _ (Matrix.posSemidef_conjTranspose_mul_self A) r).trans (gramTail_le_rectangularBest A r)

theorem lu_expectedError_best_upper {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (r : ℕ) (hr : r ≤ n) :
    NLA.RA03.expectedError A r ≤ (4:ℝ)^r*rectangularBestRankErrorSquared A r :=
  (lu_expectedError_gram_upper A r hr).trans
    (mul_le_mul_of_nonneg_left (gramTail_le_rectangularBest A r) (pow_nonneg (by norm_num) r))

#print axioms lu_expectedError_best_upper
end NLA.RA02.Paper
