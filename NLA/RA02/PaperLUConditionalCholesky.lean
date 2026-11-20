module

public import NLA.RA02.PaperLUGramVector
public import NLA.RA02.PaperCholeskyQuadratic

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem lu_conditional_cholesky_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (x : Fin n → ℂ) (j : Fin n) (hj : (A.conjTranspose*A) j j ≠ 0) :
    (∑ i, Complex.normSq (A i j) *
      (star x ⬝ᵥ (((NLA.RA03.pivotResidual A (i,j)).conjTranspose *
        NLA.RA03.pivotResidual A (i,j)) *ᵥ x)).re) ≤
      2*((A.conjTranspose*A) j j).re *
        (star x ⬝ᵥ (NLA.RA02.choleskyStep (A.conjTranspose*A) j *ᵥ x)).re := by
  let G := A.conjTranspose*A
  have hG : G.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hreal : ((G j j).re : ℂ) = G j j := by
    change (((A.conjTranspose*A) j j).re : ℂ) = (A.conjTranspose*A) j j
    rw [gram_diagonal_norm]
    rfl
  have hd : (G j j).re ≠ 0 := by
    intro hz
    apply hj
    change G j j = 0
    rw [← hreal, hz, Complex.ofReal_zero]
  have he : (star x ⬝ᵥ (NLA.RA02.choleskyStep G j *ᵥ x)).re =
      (star x ⬝ᵥ (G *ᵥ x)).re - Complex.normSq ((G *ᵥ x) j)/(G j j).re := by
    rw [choleskyStep_quadratic G hG.isHermitian x j hj, Complex.sub_re]
    rw [← hreal, Complex.div_ofReal_re, Complex.ofReal_re]
    simp only [Complex.ofReal_re]
  have hmul : 2*(G j j).re*(star x ⬝ᵥ (NLA.RA02.choleskyStep G j *ᵥ x)).re =
      2*(G j j).re*(star x ⬝ᵥ (G *ᵥ x)).re - 2*Complex.normSq ((G *ᵥ x) j) := by
    rw [he]
    field_simp [hd]
    <;> ring
  rw [hmul]
  exact lu_conditional_gram_bound A x j

theorem compression_trace_quadratics {n q : ℕ} (S : NLA.RA02.Square n)
    (U : Matrix (Fin n) (Fin q) ℂ) :
    (U.conjTranspose*S*U).trace.re =
      ∑ j, (star (fun i => U i j) ⬝ᵥ (S *ᵥ (fun i => U i j))).re := by
  have he : (U.conjTranspose*S*U).trace =
      ∑ j, star (fun i => U i j) ⬝ᵥ (S *ᵥ (fun i => U i j)) := by
    rw [Matrix.mul_assoc]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [he, Complex.re_sum]

theorem lu_conditional_compression_bound {m n q : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (U : Matrix (Fin n) (Fin q) ℂ) (j : Fin n) (hj : (A.conjTranspose*A) j j ≠ 0) :
    (∑ i, Complex.normSq (A i j) *
      (U.conjTranspose * ((NLA.RA03.pivotResidual A (i,j)).conjTranspose *
        NLA.RA03.pivotResidual A (i,j)) * U).trace.re) ≤
      2*((A.conjTranspose*A) j j).re *
        (U.conjTranspose*NLA.RA02.choleskyStep (A.conjTranspose*A) j*U).trace.re := by
  simp_rw [compression_trace_quadratics, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum (fun l _ => lu_conditional_cholesky_bound A (fun i => U i l) j hj)

#print axioms lu_conditional_compression_bound
end NLA.RA02.Paper
