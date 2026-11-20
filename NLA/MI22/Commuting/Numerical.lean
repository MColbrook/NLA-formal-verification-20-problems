module

public import NLA.MI22.PaperWitnessDefinitions
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix
open Matrix
namespace NLA.MI22.Commuting
open NLA.MI22.Paper

theorem literal_principal_minors :
    paperB 0 0 = 17 ∧
      (paperB.submatrix (fun i : Fin 2 => i.castLE (by decide)) (fun i : Fin 2 => i.castLE (by decide))).det = 278529 ∧
      paperB.det = 4096 := by
  norm_num [paperB, Matrix.det_fin_two, Matrix.det_fin_three, Matrix.submatrix_apply,
    Fin.castLE, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem literal_root_coefficient :
    (1/8:ℝ) * ((2:ℝ)^(-10:ℝ))^(-7/8:ℝ) = (2:ℝ)^(23/4:ℝ) ∧
      (2:ℝ)^(23/4:ℝ) < 64 := by
  constructor
  · rw [show (1/8:ℝ) = (2:ℝ)^(-3:ℝ) by norm_num [Real.rpow_neg],
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    norm_num
  · have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ) < 2) (by norm_num : (23/4:ℝ) < 6)
    norm_num at h ⊢
    exact h

theorem literal_error_constant :
    (32*16*(64*(10:ℝ)^(-8:ℤ))*(4^7+8*7*4^6)) = 6291456/78125 ∧
      (6291456/78125:ℝ) < 100 := by norm_num

theorem literal_matrix_product :
    witnessA * paperB = !![(4352:ℂ), -1024, 0; -1/64, 16385/256, -32; 0, -8192, 4096] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [witnessA, witnessD, paperB, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, pow_two, Matrix.diagonal_apply]

#print axioms literal_principal_minors
#print axioms literal_root_coefficient
#print axioms literal_error_constant
#print axioms literal_matrix_product
end NLA.MI22.Commuting
