module

public import NLA.MF12.PaperDyadicDefinitions
public import NLA.MF12.MatrixAlgebra
public import NLA.MF12.Parameters

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.MF12.Paper

theorem dyadic_int (z : ℤ) : IsDyadic (z : ℝ) := ⟨z, 0, by simp⟩

theorem dyadic_mul {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x*y) := by
  obtain ⟨z, k, rfl⟩ := hx
  obtain ⟨w, l, rfl⟩ := hy
  refine ⟨z*w, k+l, ?_⟩
  rw [Int.cast_mul, pow_add]
  ring

theorem dyadic_add {x y : ℝ} (hx : IsDyadic x) (hy : IsDyadic y) : IsDyadic (x+y) := by
  obtain ⟨z, k, rfl⟩ := hx
  obtain ⟨w, l, rfl⟩ := hy
  refine ⟨z*(2 : ℤ)^l+w*(2 : ℤ)^k, k+l, ?_⟩
  simp only [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, pow_add]
  field_simp

theorem dyadic_lambda_power (k : ℕ) : IsDyadic (baseLambda^k) := by
  refine ⟨1, 2*k, ?_⟩
  simp only [baseLambda, div_pow, one_pow, Int.cast_one, pow_mul]
  norm_num

theorem rational_mu_power (p k : ℕ) (hk : 1 ≤ k) (hpk : p ≤ k) :
    baseMu ((p : ℝ)/(k : ℝ))^k = baseLambda^(k-p) := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  unfold baseMu
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul_natCast baseLambda_pos.le]
  have he : (1-(p : ℝ)/(k : ℝ))*(k : ℝ) = ((k-p : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpk]
    field_simp
  rw [he, Real.rpow_natCast]

theorem powered_fractional_entries_dyadic (p k : ℕ) (hk : 1 ≤ k) (hpk : p ≤ k)
    (i j : Fin 6) : IsDyadic (((fractionalMatrix ((p : ℝ)/(k : ℝ)))^k) i j) := by
  have hzero : IsDyadic (0 : ℝ) := by simpa using dyadic_int 0
  have hone : IsDyadic (1 : ℝ) := by simpa using dyadic_int 1
  have hnat : IsDyadic (k : ℝ) := by simpa using dyadic_int (k : ℤ)
  have hlam := dyadic_lambda_power k
  have hμ : IsDyadic (baseMu ((p : ℝ)/(k : ℝ))^k) := by
    rw [rational_mu_power p k hk hpk]
    exact dyadic_lambda_power (k-p)
  rw [fractionalMatrix_power]
  fin_cases i <;> fin_cases j <;>
    first | exact hzero | exact hone | exact hlam | exact hμ | exact dyadic_mul hnat hlam | exact dyadic_mul hnat hμ

theorem reset_entries_dyadic (i j : Fin 6) : IsDyadic (resetMatrix i j) := by
  have hzero : IsDyadic (0 : ℝ) := by simpa using dyadic_int 0
  have hone : IsDyadic (1 : ℝ) := by simpa using dyadic_int 1
  have hneg : IsDyadic (-1 : ℝ) := by simpa using dyadic_int (-1)
  fin_cases i <;> fin_cases j <;>
    norm_num [resetMatrix, sourceU, sourceV, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | exact hzero | exact hone | exact hneg

#print axioms powered_fractional_entries_dyadic
#print axioms reset_entries_dyadic
end NLA.MF12.Paper
