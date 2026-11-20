module

public import NLA.MF12.PaperSharpPowerBounds
public import NLA.MF12.PaperBudget
public import NLA.MF12.Gaps

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator
namespace NLA.MF12.Paper

theorem upper_unit_norm : ‖(!![0,1;0,0] : Square 2)‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (!![0,1;0,0] : Square 2)
  have hgram : (!![0,1;0,0] : Square 2).conjTranspose * !![0,1;0,0] =
      Matrix.diagonal ![0,1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Matrix.diagonal_apply]
  rw [hgram, Matrix.l2_opNorm_diagonal] at h
  have hn : ‖(![0,1] : Fin 2 → ℝ)‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    fin_cases i <;> norm_num
  have hp := norm_nonneg (!![0,1;0,0] : Square 2)
  nlinarith

theorem triangular_sharp_norm (a z : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (hz : 0 ≤ z) :
    ‖(!![a,z;0,1] : Square 2)‖ ≤ 1+z := by
  have hd : ‖(Matrix.diagonal ![a,1] : Square 2)‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    fin_cases i
    · simpa [Real.norm_eq_abs, abs_of_nonneg ha] using ha1
    · norm_num
  have heq : (!![a,z;0,1] : Square 2) = Matrix.diagonal ![a,1] + z • !![0,1;0,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply]
  rw [heq]
  calc
    _ ≤ ‖(Matrix.diagonal ![a,1] : Square 2)‖ + ‖z • (!![0,1;0,0] : Square 2)‖ := norm_add_le _ _
    _ ≤ 1+z := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hz]
      have hu := mul_le_mul_of_nonneg_left upper_unit_norm hz
      linarith

theorem compressed_sharp_norm (lam α : ℝ) (hlam : 0 < lam) (hlamq : lam ≤ 1/4)
    (hα : 0 < α) (hα1 : α < 1) (qs : List ℕ) :
    ‖matrixProduct (qs.map (parameterCompressed lam (Real.rpow lam (1-α))))‖ ≤
      1+Real.rpow (qs.sum : ℝ) α := by
  rw [product_formula]
  have hd := diagonal_bounds lam hlam hlamq qs
  have hz := off_bounds lam α hlam hlamq hα hα1 qs
  exact (triangular_sharp_norm _ _ hd.1 hd.2 hz.1).trans (by linarith)

theorem parameter_reset_factorization (lam μ : ℝ) (q₀ qlast : ℕ) (qs : List ℕ) :
    binaryProduct (parameterMatrix lam μ) resetMatrix (gapWord (q₀ :: (qs ++ [qlast]))) =
      parameterMatrix lam μ ^ qlast * sourceV *
        matrixProduct (qs.map (parameterCompressed lam μ)) * sourceU * parameterMatrix lam μ ^ q₀ := by
  induction qs generalizing q₀ with
  | nil =>
      simp only [List.nil_append, binaryProduct_gap_head, gapWord_singleton,
        binaryProduct_replicate_false, List.map_nil,
        matrixProduct_nil, Matrix.mul_one, resetMatrix, Matrix.mul_assoc]
  | cons q qs ih =>
      rw [List.cons_append, binaryProduct_gap_head, ih q, List.map_cons, matrixProduct_cons]
      simp only [parameterCompressed, resetMatrix, Matrix.mul_assoc]

theorem parameter_factor_sharp_norm (lam μ : ℝ) (hlam : 0 < lam)
    (hμ : 0 < μ) (hlμ : lam ≤ μ) (hμ1 : μ < 1)
    (q₀ qlast : ℕ) (B : Square 2) (E : ℝ) (hE : 0 ≤ E) (hB : ‖B‖ ≤ E) :
    spectralNorm (parameterMatrix lam μ ^ qlast * sourceV * B * sourceU *
      parameterMatrix lam μ ^ q₀) ≤ Real.sqrt 6 * ((1-μ)⁻¹)^2 * E := by
  let H := (1-μ)⁻¹
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hp (q : ℕ) : ‖parameterMatrix lam μ ^ q‖ ≤ H :=
    parameter_power_sharp_norm lam μ hlam hμ hlμ hμ1 q
  have hAV : ‖parameterMatrix lam μ ^ qlast * sourceV‖ ≤ H*Real.sqrt 2 := by
    apply (Matrix.l2_opNorm_mul _ _).trans
    rw [sourceV_sharp_norm]
    exact mul_le_mul_of_nonneg_right (hp qlast) (Real.sqrt_nonneg _)
  have hAVB : ‖parameterMatrix lam μ ^ qlast * sourceV * B‖ ≤ H*Real.sqrt 2*E :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hAV hB (norm_nonneg _) (by positivity))
  have hAVBU : ‖parameterMatrix lam μ ^ qlast * sourceV * B * sourceU‖ ≤
      H*Real.sqrt 2*E*Real.sqrt 3 := by
    apply (Matrix.l2_opNorm_mul _ _).trans
    rw [sourceU_sharp_norm]
    exact mul_le_mul_of_nonneg_right hAVB (Real.sqrt_nonneg _)
  have hall := (Matrix.l2_opNorm_mul
    (parameterMatrix lam μ ^ qlast * sourceV * B * sourceU) (parameterMatrix lam μ ^ q₀)).trans
    (mul_le_mul hAVBU (hp q₀) (norm_nonneg _) (by positivity))
  have hs : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  change ‖_‖ ≤ _
  calc
    _ ≤ H*Real.sqrt 2*E*Real.sqrt 3*H := hall
    _ = Real.sqrt 6 * ((1-μ)⁻¹)^2 * E := by rw [← hs]; dsimp [H]; ring

#print axioms parameter_factor_sharp_norm
#print axioms compressed_sharp_norm
end NLA.MF12.Paper
