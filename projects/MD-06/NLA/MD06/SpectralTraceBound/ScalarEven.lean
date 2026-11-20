module

public import NLA.MD06.SpectralTraceBound.ScalarDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06SpectralTrace
open Polynomial

theorem actual_scalar_chebyshev_formula (x : ℝ) (t : ℕ) :
    ScalarTracePolynomial x t =
      2 * Real.sqrt 2 ^ t * (Chebyshev.T ℝ (t : ℤ)).eval
        (x / (2 * Real.sqrt 2)) := by
  have hd : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hd0 : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  induction t using Nat.twoStepInduction with
  | zero => simp [ScalarTracePolynomial]
  | one =>
    simp only [ScalarTracePolynomial, Nat.cast_one, Chebyshev.T_one, eval_X, pow_one]
    field_simp
  | more t ht ht1 =>
    have hc := congrArg (eval (x / (2 * Real.sqrt 2))) (Chebyshev.T_add_two ℝ (t : ℤ))
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at hc
    have hcast1 : ((t + 1 : ℕ) : ℤ) = (t : ℤ) + 1 := by omega
    have hcast2 : ((t + 2 : ℕ) : ℤ) = (t : ℤ) + 2 := by omega
    simp only [ScalarTracePolynomial, ht, ht1, hcast1, hcast2]
    rw [hc]
    simp only [pow_succ]
    field_simp
    linear_combination
      ((Chebyshev.T ℝ (t : ℤ)).eval (x / (2 * Real.sqrt 2))) * hd

theorem actual_scalar_even_square_identity (x : ℝ) (m : ℕ) :
    ScalarTracePolynomial x (2 * m) = ScalarTracePolynomial x m ^ 2 - 2 * (2 : ℝ) ^ m := by
  have hc := congrArg (eval (x / (2 * Real.sqrt 2)))
    (Chebyshev.T_mul_T ℝ (m : ℤ) (m : ℤ))
  simp only [eval_add, eval_mul, eval_ofNat, sub_self, Chebyshev.T_zero, eval_one] at hc
  have hcast : ((2 * m : ℕ) : ℤ) = (m : ℤ) + (m : ℤ) := by omega
  rw [actual_scalar_chebyshev_formula, actual_scalar_chebyshev_formula, hcast]
  rw [pow_mul, Real.sq_sqrt (by norm_num)]
  have hp : (Real.sqrt 2 ^ m) ^ 2 = (2 : ℝ) ^ m := by
    rw [← pow_mul, Nat.mul_comm m 2, pow_mul, Real.sq_sqrt (by norm_num)]
  linear_combination
    -(2 * (2 : ℝ) ^ m) * hc -
      4 * ((Chebyshev.T ℝ (m : ℤ)).eval (x / (2 * Real.sqrt 2))) ^ 2 * hp

theorem actual_scalar_even_uniform_lower_bound (x : ℝ) (m : ℕ) :
    -(2 * (2 : ℝ) ^ m) ≤ ScalarTracePolynomial x (2 * m) := by
  rw [actual_scalar_even_square_identity]
  nlinarith [sq_nonneg (ScalarTracePolynomial x m)]

#print axioms actual_scalar_chebyshev_formula
#print axioms actual_scalar_even_square_identity
#print axioms actual_scalar_even_uniform_lower_bound

end Reference.RootMD06SpectralTrace
