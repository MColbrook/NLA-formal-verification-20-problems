module

public import NLA.RA08.MatrixContour.GeneralGeometry

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set Matrix
open scoped Classical Matrix BigOperators Real MatrixOrder Matrix.Norms.L2Operator
namespace NLA.RA08.Paper.MatrixContour

theorem complexify_perturbation {n : ℕ} (B E : RealMatrix n) (t : ℝ) :
    complexify (B+t • E)=complexify B+t • complexify E := by
  change complexifyHom n (B+t • E)=_
  rw [map_add,map_smul]
  rfl

theorem small_perturbation_circle_control {n : ℕ} (B E : RealMatrix n)
    (r g t : ℝ) (hg : 0 < g) (ht : 0 ≤ t) (htg : t < g/2)
    (hE : ‖complexify E‖ ≤ 1)
    (hbase : ∀ z ∈ sphere ((r+1 : ℝ) : ℂ) r,
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify B) ∧
      ‖LiteralContour.contourResolvent (complexify B) z‖ ≤ g⁻¹) :
    ∀ z ∈ sphere ((r+1 : ℝ) : ℂ) r,
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify (B+t • E)) ∧
      ‖LiteralContour.contourResolvent (complexify (B+t • E)) z‖ ≤ 2*g⁻¹ := by
  intro z hz
  have h := LiteralContour.inverse_perturbation_control (z • (1 : Matrix (Fin n) (Fin n) ℂ)-
    complexify B) (complexify E) g t hg ht htg (hbase z hz).1 (hbase z hz).2 hE
  simpa only [complexify_perturbation,LiteralContour.contourResolvent,sub_add_eq_sub_sub] using h

theorem small_perturbation_circle_classification {n : ℕ} [NeZero n] (B E : RealMatrix n)
    (r g t : ℝ) (hr : 0 < r) (hg : 0 < g) (ht : 0 ≤ t) (htg : t < g/2) (ht1 : t < 1)
    (hE : ‖complexify E‖ ≤ 1) (hBr : ‖complexify B‖+1 < r)
    (hbase : ∀ z ∈ sphere ((r+1 : ℝ) : ℂ) r,
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify B) ∧
      ‖LiteralContour.contourResolvent (complexify B) z‖ ≤ g⁻¹)
    (x : ℝ) (hx : x ∈ spectrum ℝ (B+t • E)) :
    (x < 1 ∧ r < dist (x : ℂ) ((r+1 : ℝ) : ℂ)) ∨
      (1 < x ∧ dist (x : ℂ) ((r+1 : ℝ) : ℂ) < r) := by
  have hxC := (real_spectrum_complexify (B+t • E) x).mp hx
  have hne : x ≠ 1 := by
    intro he
    subst x
    have hu := (small_perturbation_circle_control B E r g t hg ht htg hE hbase 1
      (one_on_threshold_circle r hr.le)).1
    have hn := spectrum.mem_iff.mp hxC
    apply hn
    simpa only [Complex.ofReal_one,map_one,one_smul] using hu
  apply circle_classification_of_lt hr _ hne
  have hn : ‖complexify (B+t • E)‖ ≤ ‖complexify B‖+t := by
    rw [complexify_perturbation]
    apply (norm_add_le _ _).trans
    gcongr
    rw [norm_smul,Real.norm_of_nonneg ht]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hE ht
  have hxnorm := spectrum.norm_le_norm_of_mem hxC
  have hxabs : x ≤ ‖(x : ℂ)‖ := by simpa using le_abs_self x
  linarith

end NLA.RA08.Paper.MatrixContour
