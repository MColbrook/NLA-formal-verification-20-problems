module

public import NLA.MF12.Tensor

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace NLA.MF12.ExactTensor

theorem sum_fin_product {d e : ℕ} (g : Fin (d*e) → ℝ) :
    ∑ r, g r = ∑ i : Fin d, ∑ j : Fin e, g (finProdFinEquiv (i,j)) := by
  simpa only [Fintype.sum_prod_type] using (Equiv.sum_comp finProdFinEquiv g).symm

theorem matrix_energy_bound {d : ℕ} (A : Square d) (x : Fin d → ℝ) :
    (∑ i, (∑ j, A i j*x j)^2) ≤ (spectralNorm A)^2 * ∑ j, (x j)^2 := by
  let v : EuclideanVector d := WithLp.toLp 2 x
  have h := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A).le_opNorm v
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  simp only [← sq] at hs
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq] at hs
  exact hs

def vectorTensor {d e : ℕ} (x : EuclideanVector d) (y : EuclideanVector e) :
    EuclideanVector (d*e) :=
  WithLp.toLp 2 (fun r => x (finProdFinEquiv.symm r).1 * y (finProdFinEquiv.symm r).2)

theorem vectorTensor_apply {d e : ℕ} (x : EuclideanVector d) (y : EuclideanVector e)
    (i : Fin d) (j : Fin e) : vectorTensor x y (finProdFinEquiv (i,j)) = x i*y j := by
  simp only [vectorTensor, PiLp.toLp_apply, Equiv.symm_apply_apply]

theorem vectorTensor_norm {d e : ℕ} (x : EuclideanVector d) (y : EuclideanVector e) :
    ‖vectorTensor x y‖ = ‖x‖ * ‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
    EuclideanSpace.real_norm_sq_eq, sum_fin_product]
  simp only [vectorTensor_apply, mul_pow, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem tensor_vector_action {d e : ℕ} (A : Square d) (B : Square e)
    (x : EuclideanVector d) (y : EuclideanVector e) :
    Matrix.toEuclideanCLM (n := Fin (d*e)) (𝕜 := ℝ) (tensor A B) (vectorTensor x y) =
      vectorTensor (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x)
        (Matrix.toEuclideanCLM (n := Fin e) (𝕜 := ℝ) B y) := by
  ext r
  obtain ⟨⟨i,j⟩, rfl⟩ := finProdFinEquiv.surjective r
  change (∑ s, tensor A B (finProdFinEquiv (i,j)) s * vectorTensor x y s) =
    vectorTensor (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x)
      (Matrix.toEuclideanCLM (n := Fin e) (𝕜 := ℝ) B y) (finProdFinEquiv (i,j))
  rw [sum_fin_product, vectorTensor_apply]
  simp only [tensor_pair_apply, vectorTensor_apply]
  change (∑ k, ∑ l, A i k*B j l*(x k*y l)) =
    (∑ k, A i k*x k) * (∑ l, B j l*y l)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

#print axioms tensor_vector_action

end NLA.MF12.ExactTensor
