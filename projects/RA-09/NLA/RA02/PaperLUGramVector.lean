module

public import NLA.RA02.PaperLUConditionalVector

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem gram_diagonal_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (j : Fin n) :
    (A.conjTranspose*A) j j = ((∑ i, Complex.normSq (A i j) : ℝ) : ℂ) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]

theorem gram_quadratic_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ) (x : Fin n → ℂ) :
    star x ⬝ᵥ ((A.conjTranspose*A) *ᵥ x) =
      ((∑ i, Complex.normSq ((A *ᵥ x) i) : ℝ) : ℂ) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self,
    Complex.star_def]

theorem gram_mulVec_component {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (x : Fin n → ℂ) (j : Fin n) :
    ((A.conjTranspose*A) *ᵥ x) j = ∑ i, star (A i j)*(A *ᵥ x) i := by
  rw [← Matrix.mulVec_mulVec]
  rfl

theorem lu_conditional_gram_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (x : Fin n → ℂ) (j : Fin n) :
    (∑ i, Complex.normSq (A i j) *
      (star x ⬝ᵥ (((NLA.RA03.pivotResidual A (i,j)).conjTranspose *
        NLA.RA03.pivotResidual A (i,j)) *ᵥ x)).re) ≤
      2*((A.conjTranspose*A) j j).re * (star x ⬝ᵥ ((A.conjTranspose*A) *ᵥ x)).re -
        2*Complex.normSq (((A.conjTranspose*A) *ᵥ x) j) := by
  simp_rw [gram_quadratic_norm, gram_diagonal_norm, gram_mulVec_component, Complex.ofReal_re]
  exact lu_conditional_vector_bound A x j

#print axioms lu_conditional_gram_bound
end NLA.RA02.Paper
