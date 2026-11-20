module

public import NLA.MD06.QuantitativeCorrection.Poincare
public import NLA.MD06.QuantitativeCorrection.SliceCriticality
public import NLA.MD06.QuantitativeCorrection.GradientBounds
public import NLA.MD06.QuantitativeCorrection.RadialForce
public import NLA.MD06.QuantitativeCorrection.BoundaryRadial

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Correction
open scoped BigOperators
open Reference.MD06Actual Matrix

theorem actual_quantitative_correction_from_true_rayleigh_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hgap : ∀ z : Configuration n, (∑ i, z i) = 0 →
      gamma * ‖z‖^2 ≤ LaplacianQuadratic G (fun i => z i))
    (phi : Configuration n) (c : ℝ) (hc : 0 < c)
    (hcos : ∀ i j, G.Adj i j → c ≤ Real.cos (phi i-phi j))
    (hsmall : ‖GradientVector G phi‖ < c^2*gamma/(4*Real.sqrt 2)) :
    ∃ h : Configuration n, (∑ i, h i) = 0 ∧ ‖h‖ < c/(2*Real.sqrt 2) ∧
      (∀ i, Gradient G (PhaseLift (fun a => phi a+h a)) i = 0) ∧
      IsLocalMin (Energy G) (PhaseLift (fun a => phi a+h a)) ∧
      (∀ i j, G.Adj i j → c/2 ≤ Real.cos ((phi i+h i)-(phi j+h j))) ∧
      ∀ z : Configuration n, (∑ i, z i) = 0 →
        (c*gamma/2)*‖z‖^2 ≤ HessianQuadratic G (PhaseLift (fun a => phi a+h a)) (fun i => z i) := by
  let rho : ℝ := c/(2*Real.sqrt 2)
  have hrho : 0 < rho := by dsimp [rho];positivity
  obtain ⟨h,hzero,hnorm,hmin⟩ := actual_mean_zero_ball_energy_minimizer G phi rho hrho.le
  have hint : ‖h‖ < rho := by
    by_contra hnot
    have heq : ‖h‖ = rho := le_antisymm hnorm (not_lt.mp hnot)
    have hl := actual_correction_ball_radial_force_growth G phi h c hnorm hcos
    have hn := actual_slice_ball_minimizer_radial_force_nonpositive G phi h rho hzero hnorm hmin
    have hp := hgap h hzero
    have hb := actual_directional_force_gradient_norm_bound G phi h
    rw [heq] at hp hb
    have hlo : -(rho*‖GradientVector G phi‖) ≤ LineForce G (fun i => phi i) (fun i => h i) 0 :=
      (abs_le.mp hb).1
    have hcoeff : c^2*gamma/(4*Real.sqrt 2) = (c/2*gamma)*rho := by
      dsimp [rho]
      field_simp
      ring
    rw [hcoeff] at hsmall
    have ht := mul_lt_mul_of_pos_left hsmall hrho
    have hq := mul_le_mul_of_nonneg_left hp (show 0 ≤ c/2 by positivity)
    have hf : 0 < LineForce G (fun i => phi i) (fun i => h i) 1 := by nlinarith
    exact (not_lt_of_ge hn) hf
  have hcrit := actual_interior_slice_minimizer_gradient_zero G phi h rho hzero hint hmin
  have hedge := actual_correction_ball_edge_cosines G phi h c hint.le hcos
  have hminAngle : IsLocalMin (Energy G) (PhaseLift (fun a => phi a+h a)) := by
    apply actual_positive_cosine_critical_angle_minimum _ _ hcrit
    intro i j hij
    have hh := hedge i j hij
    have hpos : 0 < c/2 := by positivity
    simpa only [PhaseLift,← Real.Angle.coe_sub,Real.Angle.cos_coe] using lt_of_lt_of_le hpos hh
  refine ⟨h,hzero,hint,hcrit,hminAngle,hedge,?_⟩
  intro z hz
  have hh := actual_correction_ball_hessian_laplacian_lower G phi h z c hint.le hcos
  rw [actual_laplacian_quadratic_identity] at hh
  have hp := mul_le_mul_of_nonneg_left (hgap z hz) (show 0 ≤ c/2 by positivity)
  have he : c/2 * (gamma*‖z‖^2) = (c*gamma/2)*‖z‖^2 := by ring
  rw [he] at hp
  exact hp.trans hh

theorem actual_connected_quantitative_correction_constant_exists {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) :
    ∃ gamma : ℝ, 0 < gamma ∧ ∀ phi : Configuration n, ∀ c : ℝ, 0 < c →
      (∀ i j, G.Adj i j → c ≤ Real.cos (phi i-phi j)) →
      ‖GradientVector G phi‖ < c^2*gamma/(4*Real.sqrt 2) →
      ∃ h : Configuration n, (∑ i, h i) = 0 ∧ ‖h‖ < c/(2*Real.sqrt 2) ∧
        (∀ i, Gradient G (PhaseLift (fun a => phi a+h a)) i = 0) ∧
        IsLocalMin (Energy G) (PhaseLift (fun a => phi a+h a)) ∧
        (∀ i j, G.Adj i j → c/2 ≤ Real.cos ((phi i+h i)-(phi j+h j))) ∧
        ∀ z : Configuration n, (∑ i, z i) = 0 →
          (c*gamma/2)*‖z‖^2 ≤ HessianQuadratic G (PhaseLift (fun a => phi a+h a)) (fun i => z i) := by
  obtain ⟨gamma,hgamma,hgap⟩ := actual_connected_euclidean_poincare_exists G hg
  exact ⟨gamma,hgamma,fun phi c hc hcos hsmall =>
    actual_quantitative_correction_from_true_rayleigh_bound G gamma hgamma hgap phi c hc hcos hsmall⟩

#print axioms actual_quantitative_correction_from_true_rayleigh_bound
#print axioms actual_connected_quantitative_correction_constant_exists
end Reference.MD06Correction
