module

public import NLA.MD06.SpectralTraceBound.ScalarDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06SpectralTrace

theorem actual_scalar_root_sum (x : ℝ) : UpperRoot x + LowerRoot x = x := by
  dsimp [UpperRoot, LowerRoot]
  ring

theorem actual_scalar_root_product (x : ℝ) (hx : 8 ≤ x ^ 2) :
    UpperRoot x * LowerRoot x = 2 := by
  have hs := Real.sq_sqrt (show 0 ≤ x ^ 2 - 8 by linarith)
  dsimp [UpperRoot, LowerRoot]
  nlinarith

theorem actual_scalar_real_root_formula (x : ℝ) (hx : 8 ≤ x ^ 2) (t : ℕ) :
    ScalarTracePolynomial x t = UpperRoot x ^ t + LowerRoot x ^ t := by
  induction t using Nat.twoStepInduction with
  | zero => norm_num [ScalarTracePolynomial]
  | one => simpa [ScalarTracePolynomial] using (actual_scalar_root_sum x).symm
  | more t ht ht1 =>
    simp only [ScalarTracePolynomial, ht, ht1]
    calc
      x * (UpperRoot x ^ (t + 1) + LowerRoot x ^ (t + 1)) -
          2 * (UpperRoot x ^ t + LowerRoot x ^ t) =
        (UpperRoot x + LowerRoot x) *
          (UpperRoot x ^ (t + 1) + LowerRoot x ^ (t + 1)) -
          (UpperRoot x * LowerRoot x) *
            (UpperRoot x ^ t + LowerRoot x ^ t) := by
              rw [actual_scalar_root_sum, actual_scalar_root_product x hx]
      _ = UpperRoot x ^ (t + 2) + LowerRoot x ^ (t + 2) := by ring

theorem actual_scalar_lower_root_nonnegative (x : ℝ) (hx : 29 / 10 ≤ x) :
    0 ≤ LowerRoot x := by
  have hnonneg : 0 ≤ x := by linarith
  have hdisc : 0 ≤ x ^ 2 - 8 := by nlinarith
  have hs := Real.sq_sqrt hdisc
  have hsnonneg := Real.sqrt_nonneg (x ^ 2 - 8)
  dsimp [LowerRoot]
  nlinarith

theorem actual_scalar_upper_root_gap_bound (x : ℝ) (hx : 29 / 10 ≤ x) :
    GapRoot ≤ UpperRoot x := by
  have hdisc : (41 : ℝ) / 100 ≤ x ^ 2 - 8 := by nlinarith
  have hs := Real.sqrt_le_sqrt hdisc
  dsimp [GapRoot, UpperRoot]
  linarith

theorem actual_gap_root_positive : 0 < GapRoot := by
  unfold GapRoot
  positivity

theorem actual_scalar_gap_power_lower_bound (x : ℝ) (hx : 29 / 10 ≤ x) (t : ℕ) :
    GapRoot ^ t ≤ ScalarTracePolynomial x t := by
  have hdisc : 8 ≤ x ^ 2 := by nlinarith
  rw [actual_scalar_real_root_formula x hdisc t]
  have hp := pow_le_pow_left₀ (le_of_lt actual_gap_root_positive)
    (actual_scalar_upper_root_gap_bound x hx) t
  exact le_trans hp (le_add_of_nonneg_right
    (pow_nonneg (actual_scalar_lower_root_nonnegative x hx) t))

theorem actual_scalar_three_value (t : ℕ) :
    ScalarTracePolynomial 3 t = (2 : ℝ) ^ t + 1 := by
  rw [actual_scalar_real_root_formula 3 (by norm_num) t]
  norm_num [UpperRoot, LowerRoot]

#print axioms actual_scalar_root_sum
#print axioms actual_scalar_root_product
#print axioms actual_scalar_real_root_formula
#print axioms actual_scalar_lower_root_nonnegative
#print axioms actual_scalar_upper_root_gap_bound
#print axioms actual_gap_root_positive
#print axioms actual_scalar_gap_power_lower_bound
#print axioms actual_scalar_three_value

end Reference.RootMD06SpectralTrace
