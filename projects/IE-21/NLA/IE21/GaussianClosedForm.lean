module

public import NLA.IE21.GaussianTrimming
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology
namespace NLA.IE21

theorem standardGaussianDensity_derivative (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 2).exp.const_mul
    (1 / Real.sqrt (2 * Real.pi))
  have heq : gaussianPDFReal 0 1 =
      fun y : ℝ => (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-(y ^ 2) / 2) := by
    funext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, one_div]
  rw [heq]
  exact h.congr_deriv (by dsimp; ring)

theorem standardGaussianDensity_even (x : ℝ) :
    gaussianPDFReal 0 1 (-x) = gaussianPDFReal 0 1 x := by
  simp [gaussianPDFReal]

theorem standardGaussianDensity_continuous : Continuous (gaussianPDFReal 0 1) := by
  unfold gaussianPDFReal
  fun_prop

theorem gaussian_centralMass_density (a : ℝ) (ha : 0 ≤ a) :
    (gaussianReal 0 1).real {x | |x| ≤ a} =
      ∫ x in (-a)..a, gaussianPDFReal 0 1 x := by
  have hs : {x : ℝ | |x| ≤ a} = Icc (-a) a := by
    ext x
    simp only [mem_ofPred_eq, abs_le, mem_Icc]
  rw [hs, measureReal_def, gaussianReal_apply_eq_integral 0 (by norm_num),
    ENNReal.toReal_ofReal (integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x)),
    intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

theorem gaussian_truncated_density_closed_form (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in (-a)..a, x ^ 2 * gaussianPDFReal 0 1 x) =
      (gaussianReal 0 1).real {x | |x| ≤ a} - 2 * a * gaussianPDFReal 0 1 a := by
  have hderiv (x : ℝ) : HasDerivAt (fun y => y * gaussianPDFReal 0 1 y)
      (gaussianPDFReal 0 1 x - x ^ 2 * gaussianPDFReal 0 1 x) x := by
    exact ((hasDerivAt_id x).mul (standardGaussianDensity_derivative x)).congr_deriv
      (by dsimp; ring)
  have hcont : Continuous (fun x : ℝ => x ^ 2 * gaussianPDFReal 0 1 x) :=
    (continuous_id.pow 2).mul standardGaussianDensity_continuous
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc (-a) a) => hderiv x)
    ((standardGaussianDensity_continuous.sub hcont).intervalIntegrable _ _)
  rw [intervalIntegral.integral_sub (standardGaussianDensity_continuous.intervalIntegrable _ _)
    (hcont.intervalIntegrable _ _), standardGaussianDensity_even] at h
  rw [gaussian_centralMass_density a ha]
  linarith

/-- The closed form for the actual quantile-defined Gaussian second moment. -/
theorem gaussianTrim_closed_form (θ : ℝ) (hθ : 0 < θ ∧ θ < 1) :
    gaussianTrim θ = θ - 2 * gaussianCutoff θ * gaussianPDFReal 0 1 (gaussianCutoff θ) := by
  have hcut := gaussian_constant θ hθ
  have h := gaussian_truncated_density_closed_form (gaussianCutoff θ) hcut.1.le
  rw [hcut.2.1] at h
  rw [intervalIntegral.integral_of_le (by linarith [hcut.1]),
    ← integral_Icc_eq_integral_Ioc] at h
  have hf : (fun x : ℝ => x ^ 2 * gaussianPDFReal 0 1 x) =
      fun x : ℝ => (1 / Real.sqrt (2 * Real.pi)) * (x ^ 2 * Real.exp (-(x ^ 2) / 2)) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    ring
  rw [hf, integral_const_mul] at h
  exact h

#print axioms gaussianTrim_closed_form
end NLA.IE21
