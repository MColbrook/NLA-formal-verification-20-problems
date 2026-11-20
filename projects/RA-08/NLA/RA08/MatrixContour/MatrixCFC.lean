module

public import NLA.RA08.MatrixContour.DiagonalContour
public import NLA.RA08.MatrixContour.ContourConjugation
public import NLA.RA08.PaperFrobeniusCFC

@[expose] public section

set_option autoImplicit false
noncomputable section
open Complex Metric Set
open scoped Classical Matrix BigOperators Real Matrix.Norms.L2Operator
namespace NLA.RA08.Paper.MatrixContour

theorem complexify_unitary {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℝ) :
    complexify (U : RealMatrix n) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change star (complexifyHom n (U : RealMatrix n))*complexifyHom n (U : RealMatrix n)=1
  rw [← map_star,← map_mul]
  have h : star (U : RealMatrix n)*(U : RealMatrix n)=1 :=
    Unitary.star_mul_self_of_mem U.property
  rw [h,map_one]

theorem complexify_diagonal_conjugate {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℝ)
    (b : Fin n → ℝ) :
    complexify ((U : RealMatrix n)*Matrix.diagonal b*(U : RealMatrix n).transpose) =
      complexify (U : RealMatrix n)*complexify (Matrix.diagonal b)*
        star (complexify (U : RealMatrix n)) := by
  change complexifyHom n ((U : RealMatrix n)*Matrix.diagonal b*(U : RealMatrix n).transpose)=_
  rw [map_mul,map_mul]
  have hs : complexify ((U : RealMatrix n).transpose)=star (complexify (U : RealMatrix n)) := by
    simpa only [complexifyHom_apply,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using
      map_star (complexifyHom n) (U : RealMatrix n)
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℂ =>
    complexify (U : RealMatrix n)*complexify (Matrix.diagonal b)*M) hs

theorem actual_matrix_contour_clipping {n : ℕ} (A : RealMatrix n) (hA : A.IsHermitian)
    (c : ℂ) (r : ℝ) (hr : 0 < r)
    (hclass : ∀ x ∈ spectrum ℝ A,
      (x ≤ 1 ∧ r < dist (x : ℂ) c) ∨ (1 < x ∧ dist (x : ℂ) c < r)) :
    complexify (functionalCalculus witnessFunction A)=
      LiteralContour.contourClipping (complexify A) c r := by
  let U := hA.eigenvectorUnitary
  let b := hA.eigenvalues
  let W : Matrix.unitaryGroup (Fin n) ℂ := ⟨complexify (U : RealMatrix n),complexify_unitary U⟩
  let φ := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ) W
  have hb : ∀ i, (b i ≤ 1 ∧ r < dist (b i : ℂ) c) ∨ (1 < b i ∧ dist (b i : ℂ) c < r) :=
    fun i => hclass (b i) (hA.eigenvalues_mem_spectrum_real i)
  have hu : ∀ z ∈ sphere c r,
      IsUnit (z • (1 : Matrix (Fin n) (Fin n) ℂ)-complexify (Matrix.diagonal b)) := by
    intro z hz
    exact (diagonal_resolvent_unit b z (fun i => classified_off_circle (b i) c r (hb i) z hz)).1
  have hrec : A=(U : RealMatrix n)*Matrix.diagonal b*(U : RealMatrix n).transpose := by
    simpa only [U,b,Unitary.conjStarAlgAut_apply,Unitary.coe_star,Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq] using hA.spectral_theorem
  have hc : complexify A=φ (complexify (Matrix.diagonal b)) := by
    rw [hrec,complexify_diagonal_conjugate]
    rfl
  rw [hc,contourClipping_equiv φ _ c r hr hu,diagonal_contour_clipping b c r hr hb]
  rw [real_cfc_spectral_form A hA witnessFunction,complexify_diagonal_conjugate]
  rfl

#print axioms actual_matrix_contour_clipping
end NLA.RA08.Paper.MatrixContour
