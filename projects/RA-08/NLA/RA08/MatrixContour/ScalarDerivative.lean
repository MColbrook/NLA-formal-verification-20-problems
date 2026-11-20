module

public import NLA.RA08.MatrixContour.DiagonalContour

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set
open scoped Classical Real
namespace NLA.RA08.Paper.MatrixContour

theorem inverse_circle_continuous (x : ℝ) (c : ℂ) (r : ℝ)
    (hx : (x ≤ 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r)) :
    ContinuousOn (fun z : ℂ => (z-(x : ℂ))⁻¹) (sphere c r) := by
  apply (continuousOn_id.sub continuousOn_const).inv₀
  intro z hz
  exact sub_ne_zero.mpr (classified_off_circle x c r hx z hz)

theorem quotient_circle_integrable (x : ℝ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hx : (x ≤ 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r)) :
    CircleIntegrable (fun z : ℂ => (z-1)/(z-(x : ℂ))) c r := by
  have hc : ContinuousOn (fun z : ℂ => (z-1)*(z-(x : ℂ))⁻¹) (sphere c r) :=
    (continuousOn_id.sub continuousOn_const).mul (inverse_circle_continuous x c r hx)
  simpa only [div_eq_mul_inv] using hc.circleIntegrable hr

theorem outside_inverse_circle (c w : ℂ) (r : ℝ) (hr : 0 ≤ r) (hw : r < dist w c) :
    (∮ z in C(c,r), (z-w)⁻¹)=0 := by
  have hne (z : ℂ) (hz : z ∈ closedBall c r) : z-w ≠ 0 := by
    intro he
    have hzw : z=w := sub_eq_zero.mp he
    subst z
    exact (not_lt_of_ge (mem_closedBall.mp hz)) hw
  have hd : DifferentiableOn ℂ (fun z : ℂ => (z-w)⁻¹) (closedBall c r) := by
    intro z hz
    exact ((differentiableAt_id.sub_const w).inv (hne z hz)).differentiableWithinAt
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr

theorem second_pole_circle (x : ℝ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hx : (x ≤ 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r)) :
    (∮ z in C(c,r), (z-1)*((z-(x : ℂ))⁻¹)^2)=
      ∮ z in C(c,r), (z-(x : ℂ))⁻¹ := by
  have hi := (inverse_circle_continuous x c r hx).circleIntegrable hr
  have hi2 : CircleIntegrable (fun z : ℂ => ((z-(x : ℂ))⁻¹)^2) c r :=
    ((inverse_circle_continuous x c r hx).pow 2).circleIntegrable hr
  have hic : CircleIntegrable (fun z : ℂ => ((x : ℂ)-1)*((z-(x : ℂ))⁻¹)^2) c r := by
    have hc : ContinuousOn (fun z : ℂ => ((x : ℂ)-1)*((z-(x : ℂ))⁻¹)^2) (sphere c r) :=
      continuousOn_const.mul ((inverse_circle_continuous x c r hx).pow 2)
    exact hc.circleIntegrable hr
  have hz : (∮ z in C(c,r), ((z-(x : ℂ))⁻¹)^2)=0 := by
    have heq : (fun z : ℂ => (z-(x : ℂ))^(-2 : ℤ)) =
        (fun z : ℂ => ((z-(x : ℂ))⁻¹)^2) := by
      funext z
      simp only [zpow_neg,inv_pow]
      rfl
    exact (congrArg (fun f : ℂ → ℂ => circleIntegral f c r) heq).symm.trans
      (circleIntegral.integral_sub_zpow_of_ne (n := (-2 : ℤ)) (by decide) c (x : ℂ) r)
  have he : (∮ z in C(c,r), (z-1)*((z-(x : ℂ))⁻¹)^2)=
      ∮ z in C(c,r), (z-(x : ℂ))⁻¹+((x : ℂ)-1)*((z-(x : ℂ))⁻¹)^2 := by
    apply circleIntegral.integral_congr hr
    intro z hzc
    have hn : z-(x : ℂ) ≠ 0 := sub_ne_zero.mpr (classified_off_circle x c r hx z hzc)
    field_simp
    ; ring
  rw [he,circleIntegral.integral_add hi hic,circleIntegral.integral_const_mul,hz]
  simp

theorem diagonal_scalar_derivative_circle (x : ℝ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hx : (x < 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r)) :
    (clippingDividedDifference x x : ℂ)=1-(2*Real.pi*I : ℂ)⁻¹ *
      (∮ z in C(c,r), (z-1)*((z-(x : ℂ))⁻¹)^2) := by
  have hx' : (x ≤ 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r) :=
    hx.imp (fun h => ⟨h.1.le,h.2⟩) id
  rw [second_pole_circle x c r hr hx']
  rcases hx with ⟨hx,hout⟩ | ⟨hx,hin⟩
  · rw [outside_inverse_circle c (x : ℂ) r hr hout]
    simp [clippingDividedDifference,hx]
  · rw [circleIntegral.integral_sub_inv_of_mem_ball (mem_ball.mpr hin)]
    have hn : (2*Real.pi*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    rw [inv_mul_cancel₀ hn]
    simp [clippingDividedDifference,not_lt.mpr hx.le]

#print axioms diagonal_scalar_derivative_circle
end NLA.RA08.Paper.MatrixContour
