module

public import NLA.PF02.UniformPositiveOrientation.CovarianceDefinitions
public import NLA.PF02.Normalization.Normalization

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.PF02UniformPositiveOrientation
open Matrix Reference.PF02Normalization Reference.PF02Support
open scoped BigOperators MatrixOrder

theorem row_sum_congruence {p k : ℕ} (A C : Fin p → Mat (Fin k)) (S : Mat (Fin k))
    (hRows : ∀ i, C i = S.transpose * A i * S) : rowSum C = S.transpose * rowSum A * S := by
  simp only [rowSum,hRows,Matrix.mul_sum,Matrix.sum_mul]

theorem normalizing_congruence_orthogonal {p k : ℕ} (A C : Fin p → Mat (Fin k))
    (hA : ∀ i, (A i).PosSemidef) (hC : ∀ i, (C i).PosSemidef)
    (hPD : (rowSum C).PosDef) (S : Mat (Fin k))
    (hRows : ∀ i, C i = S.transpose * A i * S) :
    normalizingCongruence A C S ∈ orthogonalSet k := by
  have ha : (rootSum A).transpose = rootSum A := by
    ext i j
    simpa only [Matrix.transpose_apply,star_trivial] using (root_sum_posSemidef A).isHermitian.apply i j
  have hc : ((rootSum C)⁻¹).transpose = (rootSum C)⁻¹ := by
    ext i j
    simpa only [Matrix.transpose_apply,star_trivial] using (root_sum_posSemidef C).inv.isHermitian.apply i j
  have hu := (Matrix.isUnit_iff_isUnit_det (rootSum C)).mp (root_sum_isUnit C hPD)
  have hl := Matrix.nonsing_inv_mul (rootSum C) hu
  have hr := Matrix.mul_nonsing_inv (rootSum C) hu
  have hO : (normalizingCongruence A C S).transpose * normalizingCongruence A C S = 1 := by
    simp only [normalizingCongruence,Matrix.transpose_mul,ha,hc]
    calc
      (rootSum C)⁻¹ * (S.transpose * rootSum A) * (rootSum A * S * (rootSum C)⁻¹) =
          (rootSum C)⁻¹ * (S.transpose * (rootSum A * rootSum A) * S) * (rootSum C)⁻¹ := by
        simp only [Matrix.mul_assoc]
      _ = (rootSum C)⁻¹ * rowSum C * (rootSum C)⁻¹ := by
        rw [root_sum_sq A hA,← row_sum_congruence A C S hRows]
      _ = ((rootSum C)⁻¹ * rootSum C) * (rootSum C * (rootSum C)⁻¹) := by
        rw [← root_sum_sq C hC]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hl,hr]; simp
  exact mul_eq_one_comm.mp hO

theorem normalized_row_congruence {p k : ℕ} (A C : Fin p → Mat (Fin k))
    (hPD : (rowSum A).PosDef) (S : Mat (Fin k))
    (hRows : ∀ i, C i = S.transpose * A i * S) (i : Fin p) :
    normalizedRow C i = (normalizingCongruence A C S).transpose * normalizedRow A i * normalizingCongruence A C S := by
  have ha : (rootSum A).transpose = rootSum A := by
    ext i j
    simpa only [Matrix.transpose_apply,star_trivial] using (root_sum_posSemidef A).isHermitian.apply i j
  have hc : ((rootSum C)⁻¹).transpose = (rootSum C)⁻¹ := by
    ext i j
    simpa only [Matrix.transpose_apply,star_trivial] using (root_sum_posSemidef C).inv.isHermitian.apply i j
  have hu := (Matrix.isUnit_iff_isUnit_det (rootSum A)).mp (root_sum_isUnit A hPD)
  have hl := Matrix.nonsing_inv_mul (rootSum A) hu
  have hr := Matrix.mul_nonsing_inv (rootSum A) hu
  symm
  simp only [normalizingCongruence,normalizedRow,Matrix.transpose_mul,ha,hc]
  calc
    (rootSum C)⁻¹ * (S.transpose * rootSum A) * ((rootSum A)⁻¹ * A i * (rootSum A)⁻¹) *
        (rootSum A * S * (rootSum C)⁻¹) =
      (rootSum C)⁻¹ * S.transpose * (rootSum A * (rootSum A)⁻¹) * A i *
        ((rootSum A)⁻¹ * rootSum A) * S * (rootSum C)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (rootSum C)⁻¹ * (S.transpose * A i * S) * (rootSum C)⁻¹ := by
      rw [hl,hr]
      simp only [Matrix.mul_one,Matrix.mul_assoc]
    _ = (rootSum C)⁻¹ * C i * (rootSum C)⁻¹ := by rw [hRows i]

#print axioms row_sum_congruence
#print axioms normalizing_congruence_orthogonal
#print axioms normalized_row_congruence
end Reference.PF02UniformPositiveOrientation
