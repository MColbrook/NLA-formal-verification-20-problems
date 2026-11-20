module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace NLA.RA09.Paper

theorem gaussian_fourth_moment :
    (∫ x : ℝ, x^4 ∂gaussianReal 0 1) = 3 := by
  have h0 (t : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (s^2/2))
      (t*Real.exp (t^2/2)) t := by
    convert! (((hasDerivAt_id t).pow 2).div_const 2).exp using 1 <;> (try simp [Pi.pow_apply, Pi.mul_def, Pi.add_def]) <;> ring
  have h1 (t : ℝ) : HasDerivAt (fun s : ℝ => s*Real.exp (s^2/2))
      ((1+t^2)*Real.exp (t^2/2)) t := by
    convert! (hasDerivAt_id t).mul (h0 t) using 1 <;> (try simp [Pi.pow_apply, Pi.mul_def, Pi.add_def]) <;> ring
  have h2 (t : ℝ) : HasDerivAt (fun s : ℝ => (1+s^2)*Real.exp (s^2/2))
      ((3*t+t^3)*Real.exp (t^2/2)) t := by
    convert! (((hasDerivAt_id t).pow 2).const_add 1).mul (h0 t) using 1 <;> (try simp [Pi.pow_apply, Pi.mul_def, Pi.add_def]) <;> ring
  have h3 (t : ℝ) : HasDerivAt (fun s : ℝ => (3*s+s^3)*Real.exp (s^2/2))
      ((3+6*t^2+t^4)*Real.exp (t^2/2)) t := by
    convert! (((hasDerivAt_id t).const_mul 3).add ((hasDerivAt_id t).pow 3)).mul (h0 t)
      using 1 <;> (try simp [Pi.pow_apply, Pi.mul_def, Pi.add_def]) <;> ring
  have d0 := funext (fun t => (h0 t).deriv)
  have d1 := funext (fun t => (h1 t).deriv)
  have d2 := funext (fun t => (h2 t).deriv)
  have d3 := funext (fun t => (h3 t).deriv)
  calc
    _ = iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 1)) 0 := by
      rw [iteratedDeriv_mgf_zero] <;> simp
    _ = 3 := by
      rw [mgf_fun_id_gaussianReal]
      norm_num only [zero_mul, one_mul, zero_add, NNReal.coe_one]
      simp only [iteratedDeriv_succ, iteratedDeriv_zero, d0, d1, d2, d3]
      norm_num

theorem gaussian_second_moment :
    (∫ x : ℝ, x^2 ∂gaussianReal 0 1) = 1 := by
  have h := variance_eq_sub (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
  simpa using h.symm

theorem gaussian_square_memLp : MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 1) := by
  haveI : ENNReal.HolderTriple 4 4 2 := ⟨by apply (ENNReal.toReal_eq_toReal_iff' (by simp) (by simp)).mp; rw [ENNReal.toReal_add (by simp) (by simp)]; norm_num⟩
  simpa [pow_two, Pi.mul_apply, id_eq] using (memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by norm_num)).mul' (memLp_id_gaussianReal' (μ := 0) (v := 1) 4 (by norm_num))

theorem gaussian_square_variance : Var[fun x : ℝ => x^2; gaussianReal 0 1] = 2 := by
  rw [variance_eq_sub gaussian_square_memLp]
  change (∫ x : ℝ, (x^2)^2 ∂gaussianReal 0 1) - (∫ x : ℝ, x^2 ∂gaussianReal 0 1)^2 = 2
  have hs : (fun x : ℝ => (x^2)^2) = (fun x : ℝ => x^4) := by funext x; ring
  rw [hs]
  rw [gaussian_fourth_moment, gaussian_second_moment]
  norm_num

#print axioms gaussian_fourth_moment
#print axioms gaussian_square_variance
end NLA.RA09.Paper
