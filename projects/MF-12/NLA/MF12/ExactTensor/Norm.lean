module

public import NLA.MF12.ExactTensor.Vectors

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical

namespace NLA.MF12.ExactTensor

theorem tensor_apply_vector {d e : ℕ} (A : Square d) (B : Square e)
    (x : EuclideanVector (d*e)) (i : Fin d) (j : Fin e) :
    (Matrix.toEuclideanCLM (n := Fin (d*e)) (𝕜 := ℝ) (tensor A B) x)
        (finProdFinEquiv (i,j)) =
      ∑ k, A i k * (∑ l, B j l*x (finProdFinEquiv (k,l))) := by
  change (∑ r, tensor A B (finProdFinEquiv (i,j)) r*x r) = _
  rw [sum_fin_product]
  simp only [tensor_pair_apply, Finset.mul_sum, mul_assoc]

theorem tensor_norm_le {d e : ℕ} (A : Square d) (B : Square e) :
    spectralNorm (tensor A B) ≤ spectralNorm A * spectralNorm B := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (spectralNorm_nonneg A) (spectralNorm_nonneg B))
  intro x
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg (spectralNorm_nonneg A) (spectralNorm_nonneg B))
      (norm_nonneg x))).mp
  rw [EuclideanSpace.real_norm_sq_eq, sum_fin_product]
  simp only [tensor_apply_vector]
  calc
    (∑ i, ∑ j, (∑ k, A i k*(∑ l, B j l*x (finProdFinEquiv (k,l))))^2) =
        ∑ j, ∑ i, (∑ k, A i k*(∑ l, B j l*x (finProdFinEquiv (k,l))))^2 :=
      Finset.sum_comm
    _ ≤ ∑ j, (spectralNorm A)^2 * ∑ k, (∑ l, B j l*x (finProdFinEquiv (k,l)))^2 :=
      Finset.sum_le_sum fun j _ => matrix_energy_bound A _
    _ = (spectralNorm A)^2 * ∑ k, ∑ j, (∑ l, B j l*x (finProdFinEquiv (k,l)))^2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (spectralNorm A)^2 * ∑ k, (spectralNorm B)^2 *
        ∑ l, (x (finProdFinEquiv (k,l)))^2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact Finset.sum_le_sum fun k _ => matrix_energy_bound B _
    _ = (spectralNorm A*spectralNorm B*‖x‖)^2 := by
      rw [← Finset.mul_sum, ← sum_fin_product (fun r => (x r)^2), ← EuclideanSpace.real_norm_sq_eq]
      ring

theorem tensor_norm_ge {d e : ℕ} (A : Square d) (B : Square e) :
    spectralNorm A * spectralNorm B ≤ spectralNorm (tensor A B) := by
  let LA := Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A
  let LB := Matrix.toEuclideanCLM (n := Fin e) (𝕜 := ℝ) B
  let LT := Matrix.toEuclideanCLM (n := Fin (d*e)) (𝕜 := ℝ) (tensor A B)
  have hxy (x : EuclideanVector d) (y : EuclideanVector e) :
      ‖LA x‖ * ‖LB y‖ ≤ ‖LT‖ * (‖x‖ * ‖y‖) := by
    simpa only [LT, LA, LB, tensor_vector_action, vectorTensor_norm] using
      LT.le_opNorm (vectorTensor x y)
  have hx (x : EuclideanVector d) : ‖LA x‖ * ‖LB‖ ≤ ‖LT‖ * ‖x‖ := by
    have h := ContinuousLinearMap.opNorm_le_bound (‖LA x‖ • LB)
      (mul_nonneg (norm_nonneg LT) (norm_nonneg x)) (fun y => ?_)
    · simpa only [norm_smul, Real.norm_of_nonneg (norm_nonneg _)] using h
    · simp only [ContinuousLinearMap.smul_apply, norm_smul,
        Real.norm_of_nonneg (norm_nonneg _)]
      exact (hxy x y).trans_eq (mul_assoc _ _ _).symm
  have h := ContinuousLinearMap.opNorm_le_bound (‖LB‖ • LA) (norm_nonneg LT)
    (fun x => ?_)
  · simpa only [norm_smul, Real.norm_of_nonneg (norm_nonneg _), mul_comm, LA, LB, LT, spectralNorm] using h
  · simp only [ContinuousLinearMap.smul_apply, norm_smul,
      Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [mul_comm] using hx x

theorem actual_tensor_norm {d e : ℕ} (A : Square d) (B : Square e) :
    spectralNorm (tensor A B) = spectralNorm A * spectralNorm B :=
  le_antisymm (tensor_norm_le A B) (tensor_norm_ge A B)

#print axioms actual_tensor_norm

end NLA.MF12.ExactTensor
