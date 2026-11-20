module

public import NLA.RA09.LiteralIntegral.ChangeVariables
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Real

namespace NLA.RA09.LiteralIntegral

theorem betaIntegral_ofReal (p : ℝ) :
    Complex.betaIntegral p (1-p) =
      ((∫ u in Ioo 0 1, u ^ (p-1) * (1-u) ^ (-p) : ℝ) : ℂ) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hu0 : 0 ≤ u := hu.1.le
  have hu1 : 0 ≤ 1-u := by linarith [hu.2]
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hu0, Complex.ofReal_cpow hu1]
  push_cast
  congr 2
  ring

theorem beta_integral_value (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ u in Ioo 0 1, u ^ (p-1) * (1-u) ^ (-p)) =
      Real.pi / Real.sin (Real.pi*p) := by
  apply Complex.ofReal_injective
  rw [← betaIntegral_ofReal]
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (p:ℂ)) (t := 1-p) (by simpa using hp) (by simpa using sub_pos.mpr hp1)
  have hsum : (p:ℂ)+(1-p) = 1 := by ring
  rw [hsum, Complex.Gamma_one, one_mul, Complex.Gamma_mul_Gamma_one_sub] at h
  rw [← h]
  push_cast
  rfl

theorem normalized_kernel_integral (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ t in Ioi 0, t ^ (p-1) / (1+t)) =
      Real.pi / Real.sin (Real.pi*p) := by
  rw [← beta_integral_value p hp hp1, beta_change_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (transformed_beta_integrand p t ht).symm

#print axioms normalized_kernel_integral

end NLA.RA09.LiteralIntegral
