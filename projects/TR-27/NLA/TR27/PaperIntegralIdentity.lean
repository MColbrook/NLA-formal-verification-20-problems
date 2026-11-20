module

public import Mathlib.Algebra.Order.Chebyshev
public import NLA.TR27.PaperIntegralDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

theorem chosenPowerSum_cast (r j : ℕ) : (chosenPowerSumReal r j : ℂ) = chosenPowerSum r j := by
  simp [chosenPowerSumReal, chosenPowerSum]

theorem first_power_sum_lower (r : ℕ) : (r : ℝ) ≤ chosenPowerSumReal r 1 := by
  have h : ∑ _i : Fin r, (1 : ℝ) ≤ ∑ i : Fin r, ((i.val+1 : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast (show 1 ≤ i.val+1 by omega)
  simpa [chosenPowerSumReal] using h

theorem pivot_square_lt_second_moment {r : ℕ} (hr : 3 ≤ r) :
    (chosenPowerSumReal r 1 - 1)^2 < (r : ℝ)*chosenPowerSumReal r 2 := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun i : Fin r => ((i.val+1 : ℕ) : ℝ))
  have hlow := first_power_sum_lower r
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  simp only [Finset.card_univ, Fintype.card_fin] at hcs
  simpa only [chosenPowerSumReal, pow_one] using
    (show ((∑ i : Fin r, ((i.val+1 : ℕ) : ℝ))-1)^2 <
      (r : ℝ)*∑ i : Fin r, ((i.val+1 : ℕ) : ℝ)^2 by
      simp only [chosenPowerSumReal, pow_one] at hlow
      nlinarith)

theorem chosenPivot_ne_zero {r : ℕ} (hr : 3 ≤ r) : chosenPivot r ≠ 0 := by
  have hlow := first_power_sum_lower r
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hp : chosenPowerSumReal r 1 - 1 ≠ 0 := by linarith
  rw [chosenPivot, ← chosenPowerSum_cast]
  exact_mod_cast hp

theorem quadratic_leading_coefficient_ne_zero {r : ℕ} (hr : 3 ≤ r) :
    chosenPivot r * (chosenPivot r ^ 2 - (r : ℂ)*chosenPowerSum r 2) ≠ 0 := by
  apply mul_ne_zero (chosenPivot_ne_zero hr)
  have h := pivot_square_lt_second_moment hr
  have hn : (chosenPowerSumReal r 1 - 1)^2 - (r : ℝ)*chosenPowerSumReal r 2 ≠ 0 := by linarith
  rw [chosenPivot, ← chosenPowerSum_cast, ← chosenPowerSum_cast]
  exact_mod_cast hn

/-- The monic-quadratic precursor for arbitrary degree and chosen parameters.
F_0=b*u-r*v and F_2=b*w-S_2*v, with u*w=v^2 for homogeneous curve monomials. -/
theorem quotient_quadratic_identity (r b S u v w : ℂ) (h : u*w = v^2) :
    b*(b^2-r*S)*u^2 + ((r*S-2*b^2)*(b*u-r*v)-r^2*(b*w-S*v))*u +
      b*(b*u-r*v)^2 = 0 := by
  linear_combination -(b*r^2) * h

theorem homogeneous_monomial_identity {D : ℕ} (hD : 2 ≤ D) (s t : ℂ) :
    s^D * (s^(D-2)*t^2) = (s^(D-1)*t)^2 := by
  rw [mul_pow, ← mul_assoc, ← pow_add, ← pow_mul]
  rw [show D+(D-2) = (D-1)*2 by omega]

#print axioms quadratic_leading_coefficient_ne_zero
#print axioms quotient_quadratic_identity
end NLA.TR27.Paper
