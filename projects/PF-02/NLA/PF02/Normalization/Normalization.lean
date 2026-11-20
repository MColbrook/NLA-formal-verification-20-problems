module

public import NLA.PF02.Normalization.FullRank

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02Normalization
open Matrix Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem root_sum_posSemidef {p k : ℕ} (A : Fin p → Mat (Fin k)) : (rootSum A).PosSemidef :=
  (CFC.sqrt_nonneg (rowSum A)).posSemidef

theorem root_sum_sq {p k : ℕ} (A : Fin p → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) : rootSum A * rootSum A = rowSum A := by
  simpa only [rootSum, pow_two] using CFC.sq_sqrt (rowSum A) (psd_sum A hA).nonneg

theorem root_sum_isUnit {p k : ℕ} (A : Fin p → Mat (Fin k))
    (hsum : (rowSum A).PosDef) : IsUnit (rootSum A) :=
  (CFC.isUnit_sqrt_iff (rowSum A) hsum.posSemidef.nonneg).mpr hsum.isUnit

theorem normalized_row_posSemidef {p k : ℕ} (A : Fin p → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (i : Fin p) : (normalizedRow A i).PosSemidef := by
  have hh := (root_sum_posSemidef A).inv.isHermitian
  simpa only [normalizedRow, hh.eq] using
    (hA i).conjTranspose_mul_mul_same ((rootSum A)⁻¹)

theorem normalized_column_posSemidef {p q k : ℕ}
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (hB : ∀ j, (B j).PosSemidef) (j : Fin q) : (normalizedColumn A B j).PosSemidef := by
  have hh := (root_sum_posSemidef A).isHermitian
  simpa only [normalizedColumn, hh.eq] using
    (hB j).conjTranspose_mul_mul_same (rootSum A)

theorem normalized_row_sum {p k : ℕ} (A : Fin p → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (hsum : (rowSum A).PosDef) :
    ∑ i, normalizedRow A i = 1 := by
  have hu := (Matrix.isUnit_iff_isUnit_det (rootSum A)).mp (root_sum_isUnit A hsum)
  have hl := Matrix.nonsing_inv_mul (rootSum A) hu
  have hr := Matrix.mul_nonsing_inv (rootSum A) hu
  calc
    _ = (rootSum A)⁻¹ * rowSum A * (rootSum A)⁻¹ := by
      simp only [normalizedRow, rowSum, Matrix.mul_sum, Matrix.sum_mul]
    _ = (rootSum A)⁻¹ * (rootSum A * rootSum A) * (rootSum A)⁻¹ := by rw [root_sum_sq A hA]
    _ = ((rootSum A)⁻¹ * rootSum A) * (rootSum A * (rootSum A)⁻¹) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hl, hr]; simp

theorem normalized_trace_pairing {p q k : ℕ}
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (hsum : (rowSum A).PosDef) (i : Fin p) (j : Fin q) :
    Matrix.trace (normalizedRow A i * normalizedColumn A B j) = Matrix.trace (A i * B j) := by
  have hu := (Matrix.isUnit_iff_isUnit_det (rootSum A)).mp (root_sum_isUnit A hsum)
  have hl := Matrix.nonsing_inv_mul (rootSum A) hu
  have hr := Matrix.mul_nonsing_inv (rootSum A) hu
  have hm : normalizedRow A i * normalizedColumn A B j =
      (rootSum A)⁻¹ * (A i * B j) * rootSum A := by
    calc
      _ = (rootSum A)⁻¹ * A i * ((rootSum A)⁻¹ * rootSum A) * B j * rootSum A := by
        simp only [normalizedRow, normalizedColumn, Matrix.mul_assoc]
      _ = _ := by rw [hl]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hm, Matrix.trace_mul_cycle, hr, Matrix.one_mul]

theorem normalized_column_trace {p q k : ℕ}
    (M : Matrix (Fin p) (Fin q) ℝ)
    (A : Fin p → Mat (Fin k)) (B : Fin q → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (hsum : (rowSum A).PosDef)
    (htrace : ∀ i j, Matrix.trace (A i * B j) = M i j) (j : Fin q) :
    Matrix.trace (normalizedColumn A B j) = ∑ i, M i j := by
  calc
    _ = Matrix.trace ((∑ i, normalizedRow A i) * normalizedColumn A B j) := by rw [normalized_row_sum A hA hsum, Matrix.one_mul]
    _ = ∑ i, Matrix.trace (normalizedRow A i * normalizedColumn A B j) := by rw [Matrix.sum_mul, Matrix.trace_sum]
    _ = _ := by apply Finset.sum_congr rfl; intro i hi; rw [normalized_trace_pairing A B hsum, htrace]

#print axioms root_sum_posSemidef
#print axioms root_sum_sq
#print axioms root_sum_isUnit
#print axioms normalized_row_posSemidef
#print axioms normalized_column_posSemidef
#print axioms normalized_row_sum
#print axioms normalized_trace_pairing
#print axioms normalized_column_trace
end Reference.PF02Normalization
