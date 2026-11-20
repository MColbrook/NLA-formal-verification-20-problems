module

public import NLA.RA08.MatrixContour.GeneralRadius
public import NLA.RA08.MatrixContour.MatrixCFC

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set Matrix
open scoped Classical Matrix BigOperators Real MatrixOrder Matrix.Norms.L2Operator
namespace NLA.RA08.Paper.MatrixContour

theorem complexify_isUnit_iff {n : ℕ} (A : RealMatrix n) :
    IsUnit (complexify A) ↔ IsUnit A := by
  rw [Matrix.isUnit_iff_isUnit_det,Matrix.isUnit_iff_isUnit_det]
  have hd : (complexify A).det = (A.det : ℂ) := (Complex.ofRealHom.map_det A).symm
  rw [hd]
  simp

theorem real_spectrum_complexify {n : ℕ} (A : RealMatrix n) (x : ℝ) :
    x ∈ spectrum ℝ A ↔ (x : ℂ) ∈ spectrum ℂ (complexify A) := by
  rw [spectrum.mem_iff,spectrum.mem_iff]
  have he : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (x : ℂ)-complexify A =
      complexify (algebraMap ℝ (RealMatrix n) x-A) := by
    change _=complexifyHom n (_-_)
    rw [map_sub]
    simp only [Algebra.algebraMap_eq_smul_one,map_smul,map_one,complexifyHom_apply]
    rfl
  rw [he,complexify_isUnit_iff]

theorem diagonal_entry_le_complex_norm {n : ℕ} (b : Fin n → ℝ) (i : Fin n) :
    b i ≤ ‖complexify (Matrix.diagonal b)‖ := by
  have he : complexify (Matrix.diagonal b)=Matrix.diagonal (fun i => (b i : ℂ)) := by
    ext i j
    by_cases hij : i=j <;> simp [complexify,hij]
  rw [he,Matrix.l2_opNorm_diagonal]
  exact (le_abs_self _).trans (by simpa only [Complex.norm_real,Real.norm_eq_abs] using (norm_le_pi_norm (fun i => (b i : ℂ)) i))

theorem circle_classification_of_lt {x r : ℝ} (_hr : 0 < r) (hx : x < r+1) (hne : x ≠ 1) :
    (x < 1 ∧ r < dist (x : ℂ) ((r+1 : ℝ) : ℂ)) ∨
      (1 < x ∧ dist (x : ℂ) ((r+1 : ℝ) : ℂ) < r) := by
  rw [dist_eq_norm,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
    abs_of_neg (sub_neg.mpr hx)]
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl ⟨h,by linarith⟩
  · exact Or.inr ⟨h,by linarith⟩

theorem one_on_threshold_circle (r : ℝ) (hr : 0 ≤ r) :
    (1 : ℂ) ∈ sphere ((r+1 : ℝ) : ℂ) r := by
  rw [Metric.mem_sphere,dist_eq_norm]
  have he : (1 : ℂ)-((r+1 : ℝ) : ℂ)=((-r : ℝ) : ℂ) := by push_cast; ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr]

theorem exists_base_circle_control {n : ℕ} (b : Fin n → ℝ) (hb : ∀ i, b i ≠ 1) :
    ∃ r > 0, ∃ g > 0,
      ‖complexify (Matrix.diagonal b)‖+1 < r ∧
      (∀ i, (b i < 1 ∧ r < dist (b i : ℂ) ((r+1 : ℝ) : ℂ)) ∨
        (1 < b i ∧ dist (b i : ℂ) ((r+1 : ℝ) : ℂ) < r)) ∧
      (∀ z ∈ sphere ((r+1 : ℝ) : ℂ) r,
        IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify (Matrix.diagonal b)) ∧
        ‖LiteralContour.contourResolvent (complexify (Matrix.diagonal b)) z‖ ≤ g⁻¹) := by
  let r : ℝ := ‖complexify (Matrix.diagonal b)‖+2
  have hr : 0 < r := by dsimp [r]; positivity
  have hc : ∀ i, (b i < 1 ∧ r < dist (b i : ℂ) ((r+1 : ℝ) : ℂ)) ∨
      (1 < b i ∧ dist (b i : ℂ) ((r+1 : ℝ) : ℂ) < r) := by
    intro i
    apply circle_classification_of_lt hr _ (hb i)
    have hi := diagonal_entry_le_complex_norm b i
    dsimp [r]
    linarith
  have hu : ∀ z ∈ sphere ((r+1 : ℝ) : ℂ) r,
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify (Matrix.diagonal b)) := by
    intro z hz
    exact (diagonal_resolvent_unit b z (fun i => classified_off_circle (b i) _ r
      ((hc i).imp (fun h => ⟨h.1.le,h.2⟩) id) z hz)).1
  obtain ⟨C,hC⟩ := (isCompact_sphere ((r+1 : ℝ) : ℂ) r).exists_bound_of_continuousOn
    (LiteralContour.continuousOn_contourResolvent (complexify (Matrix.diagonal b)) _ hu)
  let K : ℝ := max C 0+1
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨r,hr,K⁻¹,inv_pos.mpr hK,by dsimp [r]; linarith,hc,?_⟩
  intro z hz
  refine ⟨hu z hz,?_⟩
  simp only [inv_inv]
  exact (hC z hz).trans (by dsimp [K]; linarith [le_max_left C 0])

end NLA.RA08.Paper.MatrixContour
