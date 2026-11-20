module

public import NLA.RA09.LiteralIntegral.BetaNormalization

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Real
open NLA.RA09.LiteralIntegral

namespace NLA.MI22.LiteralDerivative

theorem beta_derivative_ofReal (p : ℝ) :
    Complex.betaIntegral (p+1) (1-p) =
      ((∫ u in Ioo 0 1, u ^ p * (1-u) ^ (-p) : ℝ) : ℂ) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    integral_Ioc_eq_integral_Ioo, ← integral_complex_ofReal]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  have hu0 : 0 ≤ u := hu.1.le
  have hu1 : 0 ≤ 1-u := by linarith [hu.2]
  dsimp only
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hu0, Complex.ofReal_cpow hu1]
  push_cast
  congr 2 <;> ring

theorem beta_derivative_value (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ u in Ioo 0 1, u ^ p * (1-u) ^ (-p)) =
      p * (Real.pi / Real.sin (Real.pi*p)) := by
  apply Complex.ofReal_injective
  rw [← beta_derivative_ofReal]
  have h := Complex.Gamma_mul_Gamma_eq_betaIntegral
    (s := (p:ℂ)+1) (t := 1-p) (by simp; linarith) (by simpa using sub_pos.mpr hp1)
  have hsum : ((p:ℂ)+1)+(1-p) = 2 := by ring
  have htwo : Complex.Gamma 2 = 1 := by simpa using Complex.Gamma_nat_eq_factorial 1
  rw [hsum, htwo, one_mul, Complex.Gamma_add_one (p:ℂ) (by exact_mod_cast hp.ne'),
    mul_assoc, Complex.Gamma_mul_Gamma_one_sub] at h
  rw [← h]
  push_cast
  rfl

theorem transformed_derivative_beta (p t : ℝ) (ht : 0 < t) :
    (1+t)⁻¹ ^ 2 * ((t / (1+t)) ^ p * (1-t/(1+t)) ^ (-p)) =
      t ^ p / (1+t)^2 := by
  have hpos : 0 < 1+t := by linarith
  have hone : 1-t/(1+t) = (1+t)⁻¹ := by field_simp; ring
  rw [hone, Real.div_rpow ht.le hpos.le, Real.inv_rpow hpos.le,
    Real.rpow_neg hpos.le]
  have hp : (1+t)^p ≠ 0 := (Real.rpow_pos_of_pos hpos p).ne'
  field_simp

theorem unit_derivative_integral (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ t in Ioi 0, t ^ p / (1+t)^2) =
      p * (Real.pi / Real.sin (Real.pi*p)) := by
  rw [← beta_derivative_value p hp hp1, beta_change_integral]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (transformed_derivative_beta p t ht).symm

#print axioms unit_derivative_integral

end NLA.MI22.LiteralDerivative
