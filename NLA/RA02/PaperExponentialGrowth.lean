module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Filter Asymptotics
namespace NLA.RA02.Paper

theorem polynomial_littleO_exponential (q : Polynomial ℝ) :
    q.eval =o[atTop] (fun x : ℝ => Real.exp (Real.log 2 * x)) := by
  have hh : ∀ k ∈ q.support,
      (fun x : ℝ => q.coeff k * x^k) =o[atTop] (fun x : ℝ => Real.exp (Real.log 2*x)) := by
    intro k hk
    exact (isLittleO_pow_exp_pos_mul_atTop k (Real.log_pos (by norm_num : (1 : ℝ) < 2))).const_mul_left _
  have he : q.eval = ∑ k ∈ q.support, (fun x : ℝ => q.coeff k * x^k) := by
    funext x
    simp [Polynomial.eval_eq_sum, Polynomial.sum]
  rw [he]
  exact IsLittleO.sum hh

theorem exists_nat_exponential_gt {f : ℝ → ℝ}
    (hf : f =o[atTop] (fun x : ℝ => Real.exp (Real.log 2*x))) :
    ∃ r : ℕ, 1 ≤ r ∧ f r < (2 : ℝ)^r := by
  have hh := (hf.def (show (0 : ℝ) < 1/2 by norm_num)).natCast_atTop
  obtain ⟨N,hN⟩ := hh.exists_forall_of_atTop
  let r := max N 1
  have hb := hN r (Nat.le_max_left _ _)
  change ‖f r‖ ≤ (1/2 : ℝ) * ‖Real.exp (Real.log 2*(r : ℝ))‖ at hb
  have he : Real.exp (Real.log 2*(r : ℝ)) = (2 : ℝ)^r := by
    rw [mul_comm, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [he, Real.norm_eq_abs, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) r)] at hb
  refine ⟨r, Nat.le_max_right _ _, ?_⟩
  have ha := le_abs_self (f r)
  have hp := pow_pos (by norm_num : (0 : ℝ) < 2) r
  linarith

theorem polynomial_exponential_gap (q : Polynomial ℝ) :
    ∃ r : ℕ, 1 ≤ r ∧ q.eval (r : ℝ) * (2 : ℝ)^r < (4 : ℝ)^r := by
  obtain ⟨r,hr,hq⟩ := exists_nat_exponential_gt (polynomial_littleO_exponential q)
  refine ⟨r,hr,?_⟩
  calc
    q.eval (r : ℝ) * (2 : ℝ)^r < (2 : ℝ)^r * 2^r := mul_lt_mul_of_pos_right hq (by positivity)
    _ = (4 : ℝ)^r := by rw [← mul_pow]; norm_num

theorem real_power_exponential_gap (C p : ℝ) :
    ∃ r : ℕ, 1 ≤ r ∧ C * Real.rpow r p < (2 : ℝ)^r := by
  exact exists_nat_exponential_gt
    ((isLittleO_rpow_exp_pos_mul_atTop p (Real.log_pos (by norm_num : (1 : ℝ) < 2))).const_mul_left C)

end NLA.RA02.Paper
