module

public import NLA.RA02.PaperOrderedBasis

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem diagonalization_reconstruct {n : ℕ} (A : NLA.RA02.Square n)
    (V : Matrix.unitaryGroup (Fin n) ℂ) (a : Fin n → ℝ)
    (hdiag : (V : NLA.RA02.Square n).conjTranspose*A*(V : NLA.RA02.Square n) =
      Matrix.diagonal (fun i => (a i : ℂ))) :
    A = (V : NLA.RA02.Square n)*Matrix.diagonal (fun i => (a i : ℂ))*
      (V : NLA.RA02.Square n).conjTranspose := by
  have hV : (V : NLA.RA02.Square n)*(V : NLA.RA02.Square n).conjTranspose = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
  rw [← hdiag]
  calc
    A = ((V : NLA.RA02.Square n)*(V : NLA.RA02.Square n).conjTranspose)*A*
        ((V : NLA.RA02.Square n)*(V : NLA.RA02.Square n).conjTranspose) := by
      rw [hV, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem diagonalization_pivot {n : ℕ} (A : NLA.RA02.Square n)
    (V : Matrix.unitaryGroup (Fin n) ℂ) (a : Fin n → ℝ)
    (hdiag : (V : NLA.RA02.Square n).conjTranspose*A*(V : NLA.RA02.Square n) =
      Matrix.diagonal (fun i => (a i : ℂ))) (p : Fin n) :
    A p p = ((∑ i, a i*Complex.normSq (star ((V : NLA.RA02.Square n) p i)) : ℝ) : ℂ) := by
  conv_lhs => rw [diagonalization_reconstruct A V a hdiag]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self,
    Complex.star_def, map_star, star_star]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.conj_conj]
  ring

theorem unitary_column_normSq_star {n : ℕ} (V : Matrix.unitaryGroup (Fin n) ℂ) (i : Fin n) :
    ∑ p, Complex.normSq (star ((V : NLA.RA02.Square n) p i)) = 1 := by
  have hV : (V : NLA.RA02.Square n).conjTranspose*(V : NLA.RA02.Square n) = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  apply Complex.ofReal_injective
  have he := congrFun (congrFun hV i) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum,
    Complex.normSq_eq_conj_mul_self, Complex.star_def] using he

theorem sum_pivot_tail_weights {n : ℕ} (V : Matrix.unitaryGroup (Fin n) ℂ)
    (a : Fin n → ℝ) (k : ℕ) :
    (∑ p, ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val),
      a i*Complex.normSq (star ((V : NLA.RA02.Square n) p i))) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, unitary_column_normSq_star, mul_one]

#print axioms diagonalization_pivot
end NLA.RA02.Paper
