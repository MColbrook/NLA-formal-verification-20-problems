module

public import NLA.RA08.MatrixContour.ScalarDerivative

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set
open scoped Classical Real
namespace NLA.RA08.Paper.MatrixContour

theorem scalar_divided_difference_circle (x y : ℝ) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hx : (x < 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r))
    (hy : (y < 1 ∧ r < dist (y : ℂ) c) ∨ (1 < y ∧ dist (y : ℂ) c < r)) :
    (clippingDividedDifference x y : ℂ)=1-(2*Real.pi*I : ℂ)⁻¹ *
      (∮ z in C(c,r), (z-1)*((z-(x : ℂ))⁻¹*(z-(y : ℂ))⁻¹)) := by
  by_cases hxy : x=y
  · subst y
    simpa only [pow_two] using diagonal_scalar_derivative_circle x c r hr hx
  have hx' : (x ≤ 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r) :=
    hx.imp (fun h => ⟨h.1.le,h.2⟩) id
  have hy' : (y ≤ 1 ∧ r < dist (y : ℂ) c) ∨ (1 < y ∧ dist (y : ℂ) c < r) :=
    hy.imp (fun h => ⟨h.1.le,h.2⟩) id
  have hne : (x : ℂ)-(y : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hxy
  have hix := quotient_circle_integrable x c r hr hx'
  have hiy := quotient_circle_integrable y c r hr hy'
  have he : (∮ z in C(c,r), (z-1)*((z-(x : ℂ))⁻¹*(z-(y : ℂ))⁻¹)) =
      ((x : ℂ)-(y : ℂ))⁻¹ *
        ((∮ z in C(c,r), (z-1)/(z-(x : ℂ)))-(∮ z in C(c,r), (z-1)/(z-(y : ℂ)))) := by
    calc
      _ = ∮ z in C(c,r), ((x : ℂ)-(y : ℂ))⁻¹ *
          ((z-1)/(z-(x : ℂ))-(z-1)/(z-(y : ℂ))) := by
        apply circleIntegral.integral_congr hr
        intro z hz
        have hnx : z-(x : ℂ) ≠ 0 := sub_ne_zero.mpr (classified_off_circle x c r hx' z hz)
        have hny : z-(y : ℂ) ≠ 0 := sub_ne_zero.mpr (classified_off_circle y c r hy' z hz)
        field_simp
        ; ring
      _ = _ := by
        rw [circleIntegral.integral_const_mul,circleIntegral.integral_sub hix hiy]
  rw [he]
  simp only [clippingDividedDifference,if_neg hxy,Complex.ofReal_div,Complex.ofReal_sub]
  rw [LiteralContour.scalar_clipping_circle x c r hr hx',LiteralContour.scalar_clipping_circle y c r hr hy']
  field_simp
  ; ring

#print axioms scalar_divided_difference_circle
end NLA.RA08.Paper.MatrixContour
