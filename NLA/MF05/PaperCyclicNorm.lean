module

public import NLA.MF05.PaperCyclicDefinitions
public import NLA.MF05.PaperRealNorm

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical
namespace NLA.MF05.Paper.Cyclic

theorem perturbation_literal (n : ℕ) (δ : ℝ) :
    perturbation n δ = shift n + δ • corner n := by
  ext i j
  by_cases hi : i = Fin.last n
  · subst i
    have hj : ¬ n + 1 = j.val := by omega
    simp [perturbation, weight, shift, corner, Matrix.single, finRotate_last, hj, eq_comm]
  · have hlt : i.val < n := by
      have hv : i.val ≠ n := by
        intro h
        apply hi
        exact Fin.ext h
      omega
    have hr : finRotate (n + 1) i = ⟨i.val + 1, by omega⟩ := finRotate_of_lt hlt
    have hc : corner n i j = 0 := Matrix.single_apply_of_row_ne (Ne.symm hi) 0 j 1
    simp only [perturbation, weight, if_neg hi, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, hc, mul_zero, add_zero, hr, shift]
    congr 1
    simp only [Fin.ext_iff, eq_comm]

theorem perturbation_zero (n : ℕ) : perturbation n 0 = shift n := by
  rw [perturbation_literal]
  simp

theorem perturbation_apply (n : ℕ) (δ : ℝ) (x : RealVector (n+1)) (i : Fin (n+1)) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (perturbation n δ) x i =
      weight n δ i * x (finRotate (n+1) i) := by
  change (∑ j, perturbation n δ i j * x j) = _
  simp [perturbation, ite_mul]

theorem perturbation_norm_le_one (n : ℕ) (δ : ℝ) (hδ : |δ| ≤ 1) :
    realSpectralNorm (perturbation n δ) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  rw [one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  calc
    ∑ i, (Matrix.toEuclideanCLM (𝕜 := ℝ) (perturbation n δ) x i) ^ 2
        ≤ ∑ i, (x (finRotate (n+1) i)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [perturbation_apply, mul_pow]
      have hw : (weight n δ i) ^ 2 ≤ 1 := by
        by_cases hi : i = Fin.last n
        · simpa [weight, hi] using ((sq_le_one_iff_abs_le_one δ).mpr hδ)
        · simp [weight, hi]
      simpa using mul_le_mul_of_nonneg_right hw (sq_nonneg (x (finRotate (n+1) i)))
    _ = ∑ i, (x i)^2 := Equiv.sum_comp (finRotate (n+1)) (fun i => (x i)^2)

theorem perturbation_eigenvector (n : ℕ) (r : ℝ) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (perturbation n (r^(n+1))) (eigenvector n r) =
      r • eigenvector n r := by
  ext i
  rw [perturbation_apply]
  by_cases hi : i = Fin.last n
  · subst i
    simp [weight, eigenvector, finRotate_last, pow_succ, mul_comm]
  · have hlt : i.val < n := by
      have hv : i.val ≠ n := by
        intro h
        exact hi (Fin.ext h)
      omega
    have hr : finRotate (n+1) i = ⟨i.val + 1, by omega⟩ := finRotate_of_lt hlt
    simp [weight, eigenvector, hi, hr, pow_succ, mul_comm]

theorem eigenvector_ne_zero (n : ℕ) (r : ℝ) : eigenvector n r ≠ 0 := by
  intro h
  have hh := congrArg (fun x : RealVector (n+1) => x 0) h
  simpa [eigenvector] using hh

#print axioms perturbation_norm_le_one
end NLA.MF05.Paper.Cyclic
