module

public import NLA.RA08.MatrixContour.ScalarDividedDifference

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set
open scoped Classical Matrix BigOperators Real Matrix.Norms.L2Operator
namespace NLA.RA08.Paper.MatrixContour

theorem actual_diagonal_contour_derivative {n : ℕ} (b : Fin n → ℝ) (E : RealMatrix n)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hb : ∀ i, (b i < 1 ∧ r < dist (b i : ℂ) c) ∨ (1 < b i ∧ dist (b i : ℂ) c < r)) :
    complexify (clippingDerivative b E)=
      LiteralContour.contourClippingDerivative (complexify (Matrix.diagonal b)) (complexify E) c r := by
  have hb' : ∀ i, (b i ≤ 1 ∧ r < dist (b i : ℂ) c) ∨ (1 < b i ∧ dist (b i : ℂ) c < r) :=
    fun i => (hb i).imp (fun h => ⟨h.1.le,h.2⟩) id
  have hu : ∀ z ∈ sphere c r,
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify (Matrix.diagonal b)) := by
    intro z hz
    exact (diagonal_resolvent_unit b z (fun i => classified_off_circle (b i) c r (hb' i) z hz)).1
  have hi := LiteralContour.contour_derivative_integrable (complexify (Matrix.diagonal b))
    (complexify E) c r hr.le hu
  ext i j
  unfold LiteralContour.contourClippingDerivative
  rw [Matrix.sub_apply,Matrix.smul_apply,circleIntegral_matrix_entry _ c r hi]
  have he : (∮ z in C(c,r), ((z-1) •
      (LiteralContour.contourResolvent (complexify (Matrix.diagonal b)) z*complexify E*
        LiteralContour.contourResolvent (complexify (Matrix.diagonal b)) z)) i j) =
      (E i j : ℂ) * (∮ z in C(c,r), (z-1)*((z-(b i : ℂ))⁻¹*(z-(b j : ℂ))⁻¹)) := by
    calc
      _ = ∮ z in C(c,r), (E i j : ℂ)*((z-1)*((z-(b i : ℂ))⁻¹*(z-(b j : ℂ))⁻¹)) := by
        apply circleIntegral.integral_congr hr.le
        intro z hz
        have hR := (diagonal_resolvent_unit b z
          (fun l => classified_off_circle (b l) c r (hb' l) z hz)).2
        have h := congrArg (fun R : Matrix (Fin n) (Fin n) ℂ => ((z-1) • (R*complexify E*R)) i j) hR
        calc
          _ = ((z-1) • (Matrix.diagonal (fun l => (z-(b l : ℂ))⁻¹)*complexify E*
              Matrix.diagonal (fun l => (z-(b l : ℂ))⁻¹))) i j := h
          _ = _ := by
            simp only [Matrix.smul_apply,smul_eq_mul,Matrix.mul_diagonal,Matrix.diagonal_mul,
              complexify,Matrix.map_apply]
            ring
      _ = _ := circleIntegral.integral_const_mul _ _ _ _
  rw [he]
  simp only [complexify,Matrix.map_apply,clippingDerivative,Complex.ofReal_mul,smul_eq_mul]
  rw [scalar_divided_difference_circle (b i) (b j) c r hr.le (hb i) (hb j)]
  ring

#print axioms actual_diagonal_contour_derivative
end NLA.RA08.Paper.MatrixContour
