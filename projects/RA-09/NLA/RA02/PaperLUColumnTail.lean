module

public import NLA.RA02.PaperLUConditionalCholesky
public import NLA.RA02.PaperCholeskyFrameBound

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem gram_zero_column {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (j : Fin n)
    (hj : (A.conjTranspose*A) j j = 0) : ∀ i, A i j = 0 := by
  have hz : (∑ i, Complex.normSq (A i j)) = 0 := by
    have hh := congrArg Complex.re (gram_diagonal_norm A j)
    simpa [hj] using hh.symm
  intro i
  apply Complex.normSq_eq_zero.mp
  apply le_antisymm
  · have hle := Finset.single_le_sum (fun l (_ : l ∈ (Finset.univ : Finset (Fin m))) => Complex.normSq_nonneg (A l j)) (Finset.mem_univ i)
    simpa [hz] using hle
  · exact Complex.normSq_nonneg _

theorem lu_column_tail_bound {m n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n)
    (A : Matrix (Fin m) (Fin n) ℂ) (V : Matrix.unitaryGroup (Fin n) ℂ)
    (hdiag : (V : NLA.RA02.Square n).conjTranspose*(A.conjTranspose*A)*(V : NLA.RA02.Square n) =
      Matrix.diagonal (fun i => (NLA.RA02.orderedEigenvalues (A.conjTranspose*A)
        (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian i : ℂ))) (j : Fin n) :
    (∑ i, Complex.normSq (A i j) *
      NLA.RA02.rankTail ((NLA.RA03.pivotResidual A (i,j)).conjTranspose*NLA.RA03.pivotResidual A (i,j))
        (Matrix.posSemidef_conjTranspose_mul_self (NLA.RA03.pivotResidual A (i,j))).isHermitian (k-1)) ≤
      2*((A.conjTranspose*A) j j).re * NLA.RA02.rankTail (A.conjTranspose*A)
        (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian k +
      2*NLA.RA02.realTrace (A.conjTranspose*A) *
        (∑ l ∈ Finset.univ.filter (fun l : Fin n => k ≤ l.val),
          NLA.RA02.orderedEigenvalues (A.conjTranspose*A)
            (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian l *
              Complex.normSq (star ((V : NLA.RA02.Square n) j l))) := by
  let G := A.conjTranspose*A
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  let c := ∑ l ∈ Finset.univ.filter (fun l : Fin n => k ≤ l.val),
    NLA.RA02.orderedEigenvalues G hG.isHermitian l*Complex.normSq (star ((V : NLA.RA02.Square n) j l))
  have hc : 0 ≤ c := Finset.sum_nonneg (fun l _ =>
    mul_nonneg (NLA.RA02.orderedEigenvalues_nonneg G hG l) (Complex.normSq_nonneg _))
  by_cases hj : G j j = 0
  · have hzero := gram_zero_column A j hj
    simp_rw [hzero, map_zero, zero_mul, Finset.sum_const_zero]
    change 0 ≤ 2*(G j j).re*NLA.RA02.rankTail G hG.isHermitian k + 2*NLA.RA02.realTrace G*c
    rw [hj, Complex.zero_re, mul_zero, zero_mul, zero_add]
    exact mul_nonneg (mul_nonneg (by norm_num) (NLA.RA02.realTrace_nonneg hG)) hc
  · obtain ⟨U,hU,hframe⟩ := exists_cholesky_frame_bound hk hkn G hG V hdiag j hj
    have hrow : ∀ i : Fin m, NLA.RA02.rankTail
        ((NLA.RA03.pivotResidual A (i,j)).conjTranspose*NLA.RA03.pivotResidual A (i,j))
        (Matrix.posSemidef_conjTranspose_mul_self (NLA.RA03.pivotResidual A (i,j))).isHermitian (k-1) ≤
        (U.conjTranspose*((NLA.RA03.pivotResidual A (i,j)).conjTranspose*NLA.RA03.pivotResidual A (i,j))*U).trace.re := by
      intro i
      exact rankTail_le_compression_trace _ (Matrix.posSemidef_conjTranspose_mul_self _)
        (k-1) (by omega) U hU
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) =>
      mul_le_mul_of_nonneg_left (hrow i) (Complex.normSq_nonneg (A i j)))
    have hcond := lu_conditional_compression_bound A U j hj
    have hframe2 := mul_le_mul_of_nonneg_left hframe (show (0:ℝ) ≤ 2 by norm_num)
    change _ ≤ 2*(G j j).re*NLA.RA02.rankTail G hG.isHermitian k + 2*NLA.RA02.realTrace G*c
    nlinarith [hsum.trans hcond]

#print axioms lu_column_tail_bound
end NLA.RA02.Paper
