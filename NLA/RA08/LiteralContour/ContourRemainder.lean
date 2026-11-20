module

public import NLA.RA08.LiteralContour.ContourDefinitions
public import NLA.RA08.LiteralContour.Resolvent
public import Mathlib.MeasureTheory.Integral.CircleIntegral

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set
open scoped Real

namespace NLA.RA08.Paper.LiteralContour

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
local instance : NormedAlgebra ℝ A := NormedAlgebra.restrictScalars ℝ ℂ A

theorem continuousOn_contourResolvent (B : A) (s : Set ℂ)
    (hu : ∀ z ∈ s, IsUnit (z • (1 : A)-B)) : ContinuousOn (contourResolvent B) s := by
  intro z hz
  rcases hu z hz with ⟨u,hu⟩
  have h : ContinuousAt Ring.inverse (z • (1 : A)-B) := by
    rw [← hu]
    exact NormedRing.inverse_continuousAt u
  have hc : Continuous (fun z : ℂ => z • (1 : A)-B) :=
    (continuous_id.smul continuous_const).sub continuous_const
  change ContinuousWithinAt (Ring.inverse ∘ (fun z : ℂ => z • (1 : A)-B)) s z
  exact ContinuousAt.comp_continuousWithinAt (f := fun z : ℂ => z • (1 : A)-B)
    (g := Ring.inverse) h hc.continuousWithinAt

theorem contour_resolvent_integrable (B : A) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hu : ∀ z ∈ sphere c r, IsUnit (z • (1 : A)-B)) :
    CircleIntegrable (fun z => (z-1) • contourResolvent B z) c r := by
  exact ((continuousOn_id.sub continuousOn_const).smul
    (continuousOn_contourResolvent B _ hu)).circleIntegrable hr

theorem contour_derivative_integrable (B E : A) (c : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hu : ∀ z ∈ sphere c r, IsUnit (z • (1 : A)-B)) :
    CircleIntegrable (fun z => (z-1) •
      (contourResolvent B z*E*contourResolvent B z)) c r := by
  have hc := continuousOn_contourResolvent B _ hu
  exact ((continuousOn_id.sub continuousOn_const).smul
    ((hc.mul continuousOn_const).mul hc)).circleIntegrable hr

theorem contour_remainder_bound (B E : A) (c : ℂ) (d r t : ℝ)
    (hr : 0 < r) (ht : 0 ≤ t) (htr : t < r/2) (hd : ‖c-1‖ ≤ d)
    (hu : ∀ z ∈ sphere c r, IsUnit (z • (1 : A)-B))
    (hR : ∀ z ∈ sphere c r, ‖contourResolvent B z‖ ≤ r⁻¹) (hE : ‖E‖ ≤ 1) :
    ‖contourClipping (B+t • E) c r-contourClipping B c r-
      t • contourClippingDerivative B E c r‖ ≤ (2*(d+r)/r^2)*t^2 := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hup : ∀ z ∈ sphere c r, IsUnit (z • (1 : A)-(B+t • E)) := by
    intro z hz
    simpa only [sub_add_eq_sub_sub] using
      (inverse_perturbation_control (z • (1 : A)-B) E r t hr ht htr
        (hu z hz) (hR z hz) hE).1
  have hRp : ∀ z ∈ sphere c r, ‖contourResolvent (B+t • E) z‖ ≤ 2*r⁻¹ := by
    intro z hz
    simpa only [contourResolvent,sub_add_eq_sub_sub] using
      (inverse_perturbation_control (z • (1 : A)-B) E r t hr ht htr
        (hu z hz) (hR z hz) hE).2
  let δ : ℂ → A := fun z => (z-1) • (contourResolvent (B+t • E) z-
    contourResolvent B z-t • (contourResolvent B z*E*contourResolvent B z))
  have hδ : ∀ z ∈ sphere c r, δ z = (z-1) • (t^2 •
      (contourResolvent B z*E*contourResolvent B z*E*contourResolvent (B+t • E) z)) := by
    intro z hz
    have he := actual_resolvent_expansion (z • (1 : A)-B) E t (hu z hz)
      (by simpa only [sub_add_eq_sub_sub] using hup z hz)
    simp only [← sub_add_eq_sub_sub] at he
    change contourResolvent (B+t • E) z = contourResolvent B z+
      t • (contourResolvent B z*E*contourResolvent B z)+
      t^2 • (contourResolvent B z*E*contourResolvent B z*E*contourResolvent (B+t • E) z) at he
    dsimp [δ]
    conv_lhs => rw [he]
    congr 1
    abel
  have hbound : ∀ z ∈ sphere c r, ‖δ z‖ ≤ (d+r)*t^2*(2*r⁻¹^3) := by
    intro z hz
    have hz1 : ‖z-1‖ ≤ d+r := by
      calc
        ‖z-1‖ = ‖(z-c)+(c-1)‖ := by congr 1; ring
        _ ≤ ‖z-c‖+‖c-1‖ := norm_add_le _ _
        _ ≤ r+d := by rw [← dist_eq_norm,(show dist z c = r from hz)]; gcongr
        _ = d+r := by ring
    rw [hδ z hz,norm_smul,norm_smul,Real.norm_of_nonneg (sq_nonneg t)]
    have hp : ‖contourResolvent B z*E*contourResolvent B z*E*
        contourResolvent (B+t • E) z‖ ≤
        ‖contourResolvent B z‖*‖E‖*‖contourResolvent B z‖*‖E‖*
          ‖contourResolvent (B+t • E) z‖ := by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
          ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
            (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))) (norm_nonneg _))
    calc
      _ ≤ (d+r)*(t^2*(r⁻¹*1*r⁻¹*1*(2*r⁻¹))) := by
        gcongr
        exact hp.trans (by gcongr <;> first | exact hR z hz | exact hRp z hz)
      _ = _ := by ring
  have hf := contour_resolvent_integrable B c r hr.le hu
  have hfp := contour_resolvent_integrable (B+t • E) c r hr.le hup
  have hg := contour_derivative_integrable B E c r hr.le hu
  have hi : (∮ z in C(c,r), δ z) =
      (∮ z in C(c,r), (z-1) • contourResolvent (B+t • E) z)-
      (∮ z in C(c,r), (z-1) • contourResolvent B z)-
      t • (∮ z in C(c,r), (z-1) • (contourResolvent B z*E*contourResolvent B z)) := by
    have hdeltadef : δ = fun z => (z-1) • contourResolvent (B+t • E) z-
        (z-1) • contourResolvent B z-
        t • ((z-1) • (contourResolvent B z*E*contourResolvent B z)) := by
      funext z
      simp only [δ,smul_sub,smul_comm (z-1) t]
    rw [hdeltadef]
    have htg : CircleIntegrable (fun z => t •
        ((z-1) • (contourResolvent B z*E*contourResolvent B z))) c r :=
      hg.continuousOn_smul continuousOn_const
    simpa only [Pi.sub_apply,circleIntegral.integral_sub hfp hf,
      circleIntegral.integral_smul] using circleIntegral.integral_sub (hfp.sub hf) htg
  have heq : contourClipping (B+t • E) c r-contourClipping B c r-
      t • contourClippingDerivative B E c r =
      -(2*Real.pi*I : ℂ)⁻¹ • ∮ z in C(c,r), δ z := by
    rw [hi]
    dsimp only [contourClipping,contourClippingDerivative]
    simp only [smul_sub,neg_smul,smul_comm t ((2*Real.pi*I : ℂ)⁻¹)]
    abel
  rw [heq,neg_smul,norm_neg]
  calc
    _ ≤ r*((d+r)*t^2*(2*r⁻¹^3)) :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr.le hbound
    _ = _ := by field_simp

end NLA.RA08.Paper.LiteralContour
