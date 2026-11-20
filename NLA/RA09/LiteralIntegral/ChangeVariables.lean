module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace NLA.RA09.LiteralIntegral

def unitChange (t : ℝ) : ℝ := t / (1 + t)

theorem unitChange_image : unitChange '' Ioi 0 = Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨t, ht, rfl⟩
    have ht' : 0 < t := ht
    constructor
    · exact div_pos ht' (by linarith)
    · exact (div_lt_one (by linarith : 0 < 1 + t)).mpr (by linarith)
  · intro hu
    refine ⟨u / (1-u), div_pos hu.1 (by linarith [hu.2]), ?_⟩
    dsimp [unitChange]
    have h : 1-u ≠ 0 := by linarith [hu.2]
    field_simp
    ring

theorem unitChange_deriv (t : ℝ) (ht : 0 < t) :
    HasDerivAt unitChange ((1+t)⁻¹ ^ 2) t := by
  unfold unitChange
  convert!
    (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1)
      (show 1 + id t ≠ 0 by simp only [id_eq]; linarith) using 1
  simp [inv_pow]

theorem unitChange_inj : InjOn unitChange (Ioi 0) := by
  intro a ha b hb hab
  change 0 < a at ha
  change 0 < b at hb
  unfold unitChange at hab
  have h := (div_eq_div_iff (by linarith : 1+a ≠ 0) (by linarith : 1+b ≠ 0)).mp hab
  nlinarith

theorem beta_change_integral (g : ℝ → ℝ) :
    (∫ u in Ioo 0 1, g u) =
      ∫ t in Ioi 0, (1+t)⁻¹ ^ 2 * g (t / (1+t)) := by
  rw [← unitChange_image]
  convert integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun t ht => (unitChange_deriv t ht).hasDerivWithinAt) unitChange_inj g using 1
  simp only [abs_pow, sq_abs, smul_eq_mul, unitChange]

theorem transformed_beta_integrand (p t : ℝ) (ht : 0 < t) :
    (1+t)⁻¹ ^ 2 * ((t / (1+t)) ^ (p-1) * (1-t/(1+t)) ^ (-p)) =
      t ^ (p-1) / (1+t) := by
  have hpos : 0 < 1+t := by linarith
  have hone : 1-t/(1+t) = (1+t)⁻¹ := by field_simp; ring
  rw [hone, Real.div_rpow ht.le hpos.le, Real.inv_rpow hpos.le,
    Real.rpow_neg hpos.le]
  rw [Real.rpow_sub_one hpos.ne' p]
  have hp : (1+t)^p ≠ 0 := (Real.rpow_pos_of_pos hpos p).ne'
  field_simp

#print axioms beta_change_integral
#print axioms transformed_beta_integrand

end NLA.RA09.LiteralIntegral
