module

public import NLA.RA08.LiteralContour.Definitions
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set
open scoped Real

namespace NLA.RA08.Paper.LiteralContour

theorem outside_circle_integral (c w : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hw : r < dist w c) :
    (∮ z in C(c,r), (z-1)/(z-w)) = 0 := by
  have hne (z : ℂ) (hz : z ∈ closedBall c r) : z-w ≠ 0 := by
    intro he
    have hzw : z=w := sub_eq_zero.mp he
    subst z
    exact (not_lt_of_ge (mem_closedBall.mp hz)) hw
  have hd : DifferentiableOn ℂ (fun z : ℂ => (z-1)/(z-w)) (closedBall c r) := by
    intro z hz
    exact ((differentiableAt_id.sub_const 1).div (differentiableAt_id.sub_const w)
      (hne z hz)).differentiableWithinAt
  exact (hd.mono closure_ball_subset_closedBall).diffContOnCl.circleIntegral_eq_zero hr

theorem inside_circle_integral (c w : ℂ) (r : ℝ) (hw : w ∈ ball c r) :
    (2*Real.pi*Complex.I : ℂ)⁻¹ * (∮ z in C(c,r), (z-1)/(z-w)) = w-1 := by
  have hd : DifferentiableOn ℂ (fun z : ℂ => z-1) (closure (ball c r)) :=
    (differentiable_id.sub_const 1).differentiableOn
  have h := hd.diffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul hw
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

theorem scalar_clipping_circle (x : ℝ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hx : (x ≤ 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r)) :
    (witnessFunction x : ℂ) = (x : ℂ) - (2*Real.pi*Complex.I : ℂ)⁻¹ *
      (∮ z in C(c,r), (z-1)/(z-(x : ℂ))) := by
  rcases hx with ⟨hx,hout⟩ | ⟨hx,hin⟩
  · rw [outside_circle_integral c (x : ℂ) r hr hout, mul_zero, sub_zero]
    simp only [witnessFunction,min_eq_left hx]
  · rw [inside_circle_integral c (x : ℂ) r (mem_ball.mpr hin)]
    simp only [witnessFunction,min_eq_right hx.le,Complex.ofReal_one]
    ring

#print axioms scalar_clipping_circle

end NLA.RA08.Paper.LiteralContour
