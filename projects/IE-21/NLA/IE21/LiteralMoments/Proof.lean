module

public import NLA.IE21.SphericalMGF
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators RealInnerProductSpace
namespace NLA.IE21.LiteralMoments

theorem odd_product_eq_doubleFactorial (r : ℕ) :
    (∏ j ∈ Finset.range r, (2 * (j : ℝ) + 1)) =
      (Nat.doubleFactorial (2*r-1) : ℝ) := by
  induction r with
  | zero => norm_num [Nat.doubleFactorial]
  | succ r ih =>
    rw [Finset.prod_range_succ, ih]
    have hr : 2*(r+1)-1 = 2*r+1 := by omega
    rw [hr, Nat.doubleFactorial_add_one]
    push_cast
    ring

theorem actual_spherical_moment_formula (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    (∫ u, directionalEnergy x u ^ r ∂sphereLaw n) =
      ((n : ℝ)^r * (Nat.doubleFactorial (2*r-1) : ℝ)) /
        (∏ j ∈ Finset.range r, ((n : ℝ) + 2*j)) := by
  rw [NLA.IE21.spherical_moment_formula n hn x hx r, odd_product_eq_doubleFactorial]

theorem actual_spherical_moment_bound (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    (∫ u, directionalEnergy x u ^ r ∂sphereLaw n) ≤
      2^r * (Nat.factorial r : ℝ) := by
  exact NLA.IE21.spherical_moment_bound n hn x hx r

theorem actual_centered_moment_bound (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) (r : ℕ) :
    (∫ u, |directionalEnergy x u - 1| ^ r ∂sphereLaw n) ≤
      4^r * (Nat.factorial r : ℝ) := by
  exact NLA.IE21.centered_directionalEnergy_moment_bound n hn x hx r

theorem actual_spherical_mean (n : ℕ) (hn : 1 ≤ n)
    (x : Space n) (hx : ‖x‖ = 1) :
    (∫ u, directionalEnergy x u ∂sphereLaw n) = 1 := by
  exact NLA.IE21.directionalEnergy_mean n hn x hx

#print axioms actual_spherical_moment_formula
#print axioms actual_spherical_moment_bound
#print axioms actual_centered_moment_bound
#print axioms actual_spherical_mean
end NLA.IE21.LiteralMoments
