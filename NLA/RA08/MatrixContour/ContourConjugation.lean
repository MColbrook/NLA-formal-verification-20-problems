module

public import NLA.RA08.MatrixContour.CircleLinear

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set
open scoped Classical Matrix BigOperators Real Matrix.Norms.L2Operator
namespace NLA.RA08.Paper.MatrixContour

theorem ring_inverse_map_of_isUnit {A B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) (x : A) (hx : IsUnit x) : Ring.inverse (φ x)=φ (Ring.inverse x) := by
  rcases hx with ⟨u,rfl⟩
  exact (Ring.inverse_unit (Units.map φ.toMonoidHom u)).trans
    (congrArg φ (Ring.inverse_unit u)).symm

theorem contourResolvent_equiv {n : ℕ}
    (φ : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (hz : IsUnit (z • 1-A)) :
    LiteralContour.contourResolvent (φ A) z=φ (LiteralContour.contourResolvent A z) := by
  have he : φ (z • 1-A)=z • 1-φ A := by simp only [map_sub,map_smul,map_one]
  unfold LiteralContour.contourResolvent
  rw [← he]
  exact ring_inverse_map_of_isUnit φ.toAlgEquiv.toAlgHom.toRingHom _ hz

theorem contourClipping_equiv {n : ℕ}
    (φ : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hu : ∀ z ∈ sphere c r, IsUnit (z • 1-A)) :
    LiteralContour.contourClipping (φ A) c r=φ (LiteralContour.contourClipping A c r) := by
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    φ.toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap
  have hf := LiteralContour.contour_resolvent_integrable A c r hr.le hu
  have hmap := circleIntegral_clm L (fun z => (z-1) • LiteralContour.contourResolvent A z) c r hf
  have he : (∮ z in C(c,r), (z-1) • LiteralContour.contourResolvent (φ A) z) =
      ∮ z in C(c,r), φ ((z-1) • LiteralContour.contourResolvent A z) := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    exact (congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (z-1) • M)
      (contourResolvent_equiv φ A z (hu z hz))).trans
      (map_smul φ (z-1) (LiteralContour.contourResolvent A z)).symm
  unfold LiteralContour.contourClipping
  rw [map_sub,map_smul,he]
  congr 1
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (2*(Real.pi : ℂ)*I)⁻¹ • M) hmap.symm

#print axioms contourClipping_equiv
end NLA.RA08.Paper.MatrixContour
