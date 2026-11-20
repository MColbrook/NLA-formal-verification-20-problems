module

public import NLA.MI22.LiteralDerivative.Definitions
public import NLA.MI22.LiteralDerivative.BetaDerivative
public import NLA.RA09.LiteralIntegral.Proof

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Real
open NLA.RA09.LiteralIntegral

namespace NLA.MI22.LiteralDerivative

theorem derivative_integrand_bound (p m t : ℝ) (hm : 0 < m) (ht : 0 < t) :
    ‖derivativeIntegrand p m t‖ ≤ m⁻¹ * scalarIntegrand p m t := by
  have htm : 0 < t+m := by linarith
  have hscalar : m⁻¹ * scalarIntegrand p m t = t^(p-1)/(t+m) := by
    unfold scalarIntegrand
    field_simp
    <;> ring
  rw [hscalar, derivativeIntegrand, Real.norm_of_nonneg (by positivity)]
  have hpow : t^p = t^(p-1)*t := by
    rw [Real.rpow_sub_one ht.ne']
    field_simp
  rw [hpow]
  calc
    t^(p-1)*t/(t+m)^2 = (t^(p-1)/(t+m)) * (t/(t+m)) := by
      field_simp
    _ ≤ (t^(p-1)/(t+m)) * 1 := by
      gcongr
      exact (div_le_one htm).mpr (by linarith)
    _ = _ := mul_one _

theorem actual_derivative_integrable (p m : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hm : 0 < m) : IntegrableOn (derivativeIntegrand p m) (Ioi 0) := by
  have hc : ContinuousOn (derivativeIntegrand p m) (Ioi 0) := by
    intro u hu
    change 0 < u at hu
    apply ContinuousAt.continuousWithinAt
    unfold derivativeIntegrand
    fun_prop (disch := positivity)
  refine ((actual_scalar_integrable p m hp hp1 hm.le).const_mul m⁻¹).mono'
    (hc.aestronglyMeasurable measurableSet_Ioi) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi fun t ht =>
    derivative_integrand_bound p m t hm ht

theorem derivative_integrand_scaling (p m t : ℝ) (hm : 0 < m) (ht : 0 < t) :
    m * derivativeIntegrand p m (m*t) = m^(p-1) * (t^p/(1+t)^2) := by
  unfold derivativeIntegrand
  rw [Real.mul_rpow hm.le ht.le, Real.rpow_sub_one hm.ne']
  field_simp
  ring

theorem derivative_integral_value (p m : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hm : 0 < m) :
    (∫ u in Ioi 0, derivativeIntegrand p m u) =
      m^(p-1) * (p * (Real.pi / Real.sin (Real.pi*p))) := by
  have h := integral_comp_mul_left_Ioi' (derivativeIntegrand p m) 0 hm
  simp only [mul_zero, smul_eq_mul] at h
  rw [← h, ← integral_const_mul, ← unit_derivative_integral p hp hp1,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact derivative_integrand_scaling p m t hm ht

theorem actual_literal_derivative_formula (p m : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hm : 0 < m) :
    (Real.sin (Real.pi*p) / Real.pi) *
      (∫ u in Ioi 0, u^p / (u+m)^2) = p * m^(p-1) := by
  change normalization p * (∫ u in Ioi 0, derivativeIntegrand p m u) = _
  rw [derivative_integral_value p m hp hp1 hm, normalization]
  have hs : Real.sin (Real.pi*p) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hp)
      (by nlinarith [Real.pi_pos])).ne'
  field_simp

#print axioms actual_derivative_integrable
#print axioms actual_literal_derivative_formula

end NLA.MI22.LiteralDerivative
