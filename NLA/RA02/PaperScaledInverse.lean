module

public import NLA.RA02.PaperInverseDefinitions
public import NLA.RA02.PaperPrefixInverse

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical Topology
open Filter
namespace NLA.RA02.Paper

theorem scaledFamilyInverse_eq (r : ℕ) {t : ℝ} (ht : t ≠ 0) :
    scaledFamilyInverse r t = epsilon (r+1) t^r • (sharpFamily (r+1) t)⁻¹ := by
  have he : epsilon (r+1) t ≠ 0 := pow_ne_zero _ ht
  have hd : (diagonalScales (r+1) t)⁻¹ =
      Matrix.diagonal (fun i : Fin (r+1) => (epsilon (r+1) t^i.val)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [diagonalScales, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [he]
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [sharpFamily, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hd, ← Matrix.transpose_nonsing_inv]
  rw [← Matrix.mul_smul, ← Matrix.smul_mul, ← Matrix.mul_assoc]
  unfold scaledFamilyInverse
  congr 2
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
    exact pow_sub₀ _ he (by omega)
  · simp [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, hij]

theorem lower_inverse_continuousAt_zero (n : ℕ) :
    ContinuousAt (fun t : ℝ => (lower n t)⁻¹) 0 := by
  apply (continuousAt_matrix_inv _ _).comp (continuous_lower n).continuousAt
  simpa only [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv] using
    (continuousAt_inv₀ (show (lower n 0).det ≠ 0 by rw [lower_det]; exact one_ne_zero))

theorem scaledFamilyInverse_continuousAt_zero (r : ℕ) : ContinuousAt (scaledFamilyInverse r) 0 := by
  have hi := lower_inverse_continuousAt_zero (r+1)
  have ht := (continuous_id.matrix_transpose.continuousAt).comp hi
  have hd : Continuous (fun t : ℝ => Matrix.diagonal (fun i : Fin (r+1) => epsilon (r+1) t^(r-i.val))) := by
    apply continuous_matrix
    intro i j
    simp only [Matrix.diagonal_apply, epsilon]
    split_ifs <;> fun_prop
  exact (ht.mul hd.continuousAt).mul hi

theorem scaledFamilyInverse_zero (r : ℕ) : scaledFamilyInverse r 0 = lastCoordinateProjection r := by
  simp only [scaledFamilyInverse, lower_zero, inv_one, Matrix.transpose_one,
    Matrix.one_mul, Matrix.mul_one, lastCoordinateProjection]
  congr 1
  funext i
  by_cases hi : i = Fin.last r
  · subst i
    simp [epsilon]
  · have hv : i.val < r := by
      have hlt := i.isLt
      have hn : i.val ≠ r := fun h => hi (Fin.ext h)
      omega
    have hn : r-i.val ≠ 0 := by omega
    simp [lastCoordinateProjection, epsilon, Pi.single_apply, hi, hn]

theorem scaledFamilyInverse_limit (r : ℕ) :
    Tendsto (scaledFamilyInverse r) (𝓝[>] 0) (𝓝 (lastCoordinateProjection r)) := by
  rw [← scaledFamilyInverse_zero]
  exact (scaledFamilyInverse_continuousAt_zero r).tendsto.mono_left inf_le_left

#print axioms scaledFamilyInverse_limit
end NLA.RA02.Paper
