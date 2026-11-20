module

public import NLA.RA09.LiteralIntegral.BetaNormalization
public import NLA.RA09.LiteralIntegral.Definitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped Real

namespace NLA.RA09.LiteralIntegral

theorem normalization_pos (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    0 < normalization p := by
  exact div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hp)
    (by nlinarith [Real.pi_pos])) Real.pi_pos

theorem scalarIntegrand_eq_library (p x t : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hx : 0 ≤ x) (ht : 0 < t) :
    scalarIntegrand p x t = Real.rpowIntegrand₀₁ p t x := by
  rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hp, hp1⟩ ht.le hx]
  simp only [scalarIntegrand, div_eq_mul_inv, add_comm]

theorem actual_scalar_integrable (p x : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hx : 0 ≤ x) : IntegrableOn (scalarIntegrand p x) (Ioi 0) := by
  refine (Real.integrableOn_rpowIntegrand₀₁_Ioi ⟨hp,hp1⟩ hx).congr_fun ?_
    measurableSet_Ioi
  intro t ht
  exact (scalarIntegrand_eq_library p x t hp hp1 hx ht).symm

theorem library_constant (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    (∫ t in Ioi 0, Real.rpowIntegrand₀₁ p t 1) =
      Real.pi / Real.sin (Real.pi*p) := by
  rw [← normalized_kernel_integral p hp hp1]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.rpowIntegrand₀₁_eq_pow_div ⟨hp,hp1⟩ ht.le (by norm_num)]
  simp only [mul_one, add_comm]

theorem actual_scalar_integral_representation (p x : ℝ) (hp : 0 < p)
    (hp1 : p < 1) (hx : 0 ≤ x) :
    x ^ p = normalization p * ∫ t in Ioi 0, scalarIntegrand p x t := by
  rw [Real.rpow_eq_const_mul_integral ⟨hp,hp1⟩ hx, library_constant p hp hp1,
    inv_div, normalization]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  exact (scalarIntegrand_eq_library p x t hp hp1 hx ht).symm

theorem actual_literal_scalar_formula (p x : ℝ) (hp : 0 < p)
    (hp1 : p < 1) (hx : 0 ≤ x) :
    x ^ p = (Real.sin (Real.pi*p) / Real.pi) *
      ∫ t in Ioi 0, t ^ (p-1) * x * (x+t)⁻¹ :=
  actual_scalar_integral_representation p x hp hp1 hx

#print axioms actual_scalar_integrable
#print axioms actual_literal_scalar_formula
#print axioms normalization_pos

end NLA.RA09.LiteralIntegral
