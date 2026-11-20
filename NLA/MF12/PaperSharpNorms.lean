module

public import NLA.MF12.PaperAlgebra
public import NLA.MF12.Norms

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Matrix.Norms.L2Operator
namespace NLA.MF12.Paper

theorem sourceV_gram : sourceV.conjTranspose * sourceV = Matrix.diagonal ![2,2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceV, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem sourceU_gram : sourceU * sourceU.conjTranspose = Matrix.diagonal ![3,1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceU, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem sourceV_sharp_norm : ‖sourceV‖ = Real.sqrt 2 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self sourceV
  rw [sourceV_gram, Matrix.l2_opNorm_diagonal] at h
  have hn : ‖(![2,2] : Fin 2 → ℝ)‖ = 2 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)).mpr
      intro i
      fin_cases i <;> norm_num
    · simpa using norm_le_pi_norm (![2,2] : Fin 2 → ℝ) 0
  rw [hn] at h
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hp := norm_nonneg sourceV
  have hsp := Real.sqrt_nonneg (2:ℝ)
  nlinarith

theorem sourceU_sharp_norm : ‖sourceU‖ = Real.sqrt 3 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self sourceU.conjTranspose
  rw [Matrix.conjTranspose_conjTranspose, sourceU_gram,
    Matrix.l2_opNorm_diagonal, Matrix.l2_opNorm_conjTranspose] at h
  have hn : ‖(![3,1] : Fin 2 → ℝ)‖ = 3 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 3)).mpr
      intro i
      fin_cases i <;> norm_num
    · simpa using norm_le_pi_norm (![3,1] : Fin 2 → ℝ) 0
  rw [hn] at h
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hp := norm_nonneg sourceU
  have hsp := Real.sqrt_nonneg (3:ℝ)
  nlinarith

#print axioms sourceV_sharp_norm
#print axioms sourceU_sharp_norm
end NLA.MF12.Paper
