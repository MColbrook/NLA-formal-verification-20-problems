module

public import NLA.RA08.MatrixContour.CircleLinear

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set
open scoped Classical Matrix BigOperators Real Matrix.Norms.L2Operator
namespace NLA.RA08.Paper.MatrixContour

theorem diagonal_resolvent_unit {n : ℕ} (b : Fin n → ℝ) (z : ℂ)
    (hz : ∀ i, z ≠ (b i : ℂ)) :
    IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify (Matrix.diagonal b)) ∧
    LiteralContour.contourResolvent (complexify (Matrix.diagonal b)) z =
      Matrix.diagonal (fun i => (z-(b i : ℂ))⁻¹) := by
  let d : Fin n → ℂ := fun i => z-(b i : ℂ)
  have hd : ∀ i, d i ≠ 0 := fun i => sub_ne_zero.mpr (hz i)
  have hm : Matrix.diagonal d*Matrix.diagonal (fun i => (d i)⁻¹)=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]
  have hm' : Matrix.diagonal (fun i => (d i)⁻¹)*Matrix.diagonal d=1 := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨Matrix.diagonal d,Matrix.diagonal (fun i => (d i)⁻¹),hm,hm'⟩
  have he : z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify (Matrix.diagonal b)=Matrix.diagonal d := by
    ext i j
    by_cases hij : i=j
    · subst j; simp [complexify,d]
    · simp [complexify,d,hij]
  constructor
  · rw [he]; exact u.isUnit
  · unfold LiteralContour.contourResolvent
    rw [he]
    exact Ring.inverse_unit u

theorem classified_off_circle (x : ℝ) (c : ℂ) (r : ℝ)
    (hx : (x ≤ 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r))
    (z : ℂ) (hz : z ∈ sphere c r) : z ≠ (x : ℂ) := by
  intro he
  subst z
  have hdist := Metric.mem_sphere.mp hz
  rcases hx with hx | hx <;> linarith [hx.2]

theorem diagonal_contour_clipping {n : ℕ} (b : Fin n → ℝ) (c : ℂ) (r : ℝ)
    (hr : 0 < r)
    (hb : ∀ i, (b i ≤ 1 ∧ r < dist (b i : ℂ) c) ∨ (1 < b i ∧ dist (b i : ℂ) c < r)) :
    LiteralContour.contourClipping (complexify (Matrix.diagonal b)) c r =
      complexify (Matrix.diagonal (fun i => witnessFunction (b i))) := by
  have hu : ∀ z ∈ sphere c r,
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify (Matrix.diagonal b)) := by
    intro z hz
    exact (diagonal_resolvent_unit b z (fun i => classified_off_circle (b i) c r (hb i) z hz)).1
  have hi := LiteralContour.contour_resolvent_integrable (complexify (Matrix.diagonal b)) c r hr.le hu
  ext i j
  unfold LiteralContour.contourClipping
  rw [Matrix.sub_apply,Matrix.smul_apply,circleIntegral_matrix_entry _ c r hi]
  have he : (∮ z in C(c,r), ((z-1) • LiteralContour.contourResolvent (complexify (Matrix.diagonal b)) z) i j) =
      ∮ z in C(c,r), ((z-1) • Matrix.diagonal (fun l => (z-(b l : ℂ))⁻¹)) i j := by
    apply circleIntegral.integral_congr hr.le
    intro z hz
    exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => ((z-1) • M) i j)
      (diagonal_resolvent_unit b z (fun l => classified_off_circle (b l) c r (hb l) z hz)).2
  rw [he]
  by_cases hij : i=j
  · subst j
    simpa only [complexify,Matrix.map_apply,Matrix.diagonal_apply_eq,Matrix.smul_apply,
      smul_eq_mul,div_eq_mul_inv] using (LiteralContour.scalar_clipping_circle (b i) c r hr.le (hb i)).symm
  · simp [complexify,hij,circleIntegral]

#print axioms diagonal_contour_clipping
end NLA.RA08.Paper.MatrixContour
