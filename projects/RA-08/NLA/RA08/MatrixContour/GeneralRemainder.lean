module

public import NLA.RA08.MatrixContour.GeneralStability

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set Matrix
open scoped Classical Matrix BigOperators Real MatrixOrder Matrix.Norms.L2Operator
namespace NLA.RA08.Paper.MatrixContour

theorem normalized_general_contour_remainder {n : ℕ} [NeZero n]
    (b : Fin n → ℝ) (hb : ∀ i, b i ≠ 1) (E : RealMatrix n)
    (hE : E.IsHermitian) (hEnorm : ‖complexify E‖ ≤ 1) :
    ∃ δ > 0, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → t < δ →
      spectralNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E)
          ≤ C*t^2 := by
  obtain ⟨r,hr,g,hg,hBr,hclass,hbase⟩ := exists_base_circle_control b hb
  refine ⟨min (g/2) 1,lt_min (by positivity) zero_lt_one,4*r^2/g^3,by positivity,?_⟩
  intro t ht htd
  have htg : t < g/2 := htd.trans_le (min_le_left _ _)
  have ht1 : t < 1 := htd.trans_le (min_le_right _ _)
  have hB := Matrix.isHermitian_diagonal b
  have hA : (Matrix.diagonal b+t • E).IsHermitian := hB.add (hE.smul (IsSelfAdjoint.all t))
  have hfA := actual_matrix_contour_clipping (Matrix.diagonal b+t • E) hA
    ((r+1 : ℝ) : ℂ) r hr (fun x hx =>
      (small_perturbation_circle_classification (Matrix.diagonal b) E r g t hr hg ht htg ht1
        hEnorm hBr hbase x hx).imp (fun h => ⟨h.1.le,h.2⟩) id)
  have hfB := actual_matrix_contour_clipping (Matrix.diagonal b) hB ((r+1 : ℝ) : ℂ) r hr
    (by
      intro x hx
      rw [spectrum_diagonal] at hx
      obtain ⟨i,rfl⟩ := hx
      exact (hclass i).imp (fun h => ⟨h.1.le,h.2⟩) id)
  have hD := actual_diagonal_contour_derivative b E ((r+1 : ℝ) : ℂ) r hr hclass
  have hd : ‖((r+1 : ℝ) : ℂ)-1‖ ≤ r := by
    have he : ((r+1 : ℝ) : ℂ)-1=(r : ℂ) := by push_cast; ring
    rw [he,Complex.norm_real,Real.norm_of_nonneg hr.le]
  have hc := contour_remainder_bound_separate_radius (complexify (Matrix.diagonal b))
    (complexify E) ((r+1 : ℝ) : ℂ) r r g t hr hg ht htg hd
    (fun z hz => (hbase z hz).1) (fun z hz => (hbase z hz).2) hEnorm
  have he : complexify (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
      functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E)=
      LiteralContour.contourClipping (complexify (Matrix.diagonal b)+t • complexify E)
        ((r+1 : ℝ) : ℂ) r-
      LiteralContour.contourClipping (complexify (Matrix.diagonal b)) ((r+1 : ℝ) : ℂ) r-
      t • LiteralContour.contourClippingDerivative (complexify (Matrix.diagonal b))
        (complexify E) ((r+1 : ℝ) : ℂ) r := by
    change complexifyHom n (_-_-t • _)=_
    rw [map_sub,map_sub,map_smul]
    simp only [complexifyHom_apply,hfA,hfB,hD,complexify_perturbation]
  calc
    _ ≤ ‖complexify (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E)‖ :=
      spectralNorm_le_complexify_norm _
    _ = _ := congrArg norm he
    _ ≤ (4*r^2/g^3)*t^2 := by convert hc using 1; ring

theorem clippingDerivative_smul {n : ℕ} (b : Fin n → ℝ) (E : RealMatrix n) (s : ℝ) :
    clippingDerivative b (s • E)=s • clippingDerivative b E := by
  ext i j
  simp only [clippingDerivative,Matrix.smul_apply,smul_eq_mul]
  ring

theorem general_contour_remainder {n : ℕ} [NeZero n]
    (b : Fin n → ℝ) (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) (hE : E.IsHermitian) :
    ∃ δ > 0, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → t < δ →
      spectralNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E)
          ≤ C*t^2 := by
  let M : ℝ := ‖complexify E‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  let En : RealMatrix n := M⁻¹ • E
  have hEn : En.IsHermitian := hE.smul (IsSelfAdjoint.all _)
  have hEnorm : ‖complexify En‖ ≤ 1 := by
    change ‖complexifyHom n (M⁻¹ • E)‖ ≤ 1
    rw [map_smul,complexifyHom_apply,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hM.le)]
    apply (inv_mul_le_iff₀ hM).mpr
    dsimp [M]
    linarith
  obtain ⟨δ,hδ,C,hC,hbound⟩ := normalized_general_contour_remainder b hb En hEn hEnorm
  refine ⟨δ/M,div_pos hδ hM,C*M^2,mul_pos hC (sq_pos_of_pos hM),?_⟩
  intro t ht htd
  have htM : t*M < δ := (lt_div_iff₀ hM).mp htd
  have hn := hbound (t*M) (mul_nonneg ht hM.le) htM
  have hscale : (t*M) • En=t • E := by
    dsimp [En]
    rw [smul_smul]
    congr 1
    field_simp
  have hD : (t*M) • clippingDerivative b En=t • clippingDerivative b E := by
    dsimp [En]
    rw [clippingDerivative_smul,smul_smul]
    congr 1
    field_simp
  rw [hscale,hD] at hn
  convert hn using 1; ring

#print axioms general_contour_remainder

theorem general_contour_remainder_all_dimensions {n : ℕ}
    (b : Fin n → ℝ) (hb : ∀ i, b i ≠ 1) (E : RealMatrix n) (hE : E.IsHermitian) :
    ∃ δ > 0, ∃ C > 0, ∀ t : ℝ, 0 ≤ t → t < δ →
      spectralNorm (functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E)
          ≤ C*t^2 := by
  by_cases hn : n=0
  · subst n
    refine ⟨1,zero_lt_one,1,zero_lt_one,?_⟩
    intro t _ _
    have he : functionalCalculus witnessFunction (Matrix.diagonal b+t • E)-
        functionalCalculus witnessFunction (Matrix.diagonal b)-t • clippingDerivative b E =
          (0 : RealMatrix 0) := Subsingleton.elim _ _
    rw [he]
    simpa [spectralNorm] using sq_nonneg t
  · have : NeZero n := ⟨hn⟩
    exact general_contour_remainder b hb E hE

#print axioms general_contour_remainder_all_dimensions
end NLA.RA08.Paper.MatrixContour
