module

public import NLA.RA09.Paper.Pseudoinverse

@[expose] public section

/-! The manuscript's harmonic constraint in actual matrix coordinates. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder
open Matrix
namespace NLA.RA09.Paper

private theorem orthogonal_dot {n : ℕ} (U : Matrix.unitaryGroup (Fin n) ℝ)
    (v w : Fin n → ℝ) :
    ((U : RealMatrix n).transpose *ᵥ v) ⬝ᵥ ((U : RealMatrix n).transpose *ᵥ w) = v ⬝ᵥ w := by
  rw [dotProduct_transpose_mulVec, mulVec_mulVec, orthogonal_mul_transpose, one_mulVec,
    dotProduct_comm]

theorem harmonic_matrix {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℝ) (b : ℝ) (hv : ∑ i, v i^2 = 1) (hb : 0 < b)
    (horder : b • outerSquare v ≤ A) :
    v ∈ Set.range (fun x : Fin n → ℝ => A *ᵥ x) ∧
      b * (v ⬝ᵥ (spectralPseudoinverse A *ᵥ v)) ≤ 1 := by
  let U : RealMatrix n := d.orthogonal
  let w : Fin n → ℝ := U.transpose *ᵥ v
  have hA : A = spectralCombination d d.eigenvalues := d.reconstruct
  have hdiag : U.transpose*A*U = diagonal d.eigenvalues := by
    exact (congrArg (fun M : RealMatrix n => U.transpose*M*U) d.reconstruct).trans
      (spectralCombination_conjugate d d.eigenvalues)
  have hconj := (sub_nonneg.mpr horder).posSemidef.conjTranspose_mul_mul_same U
  have hD : (diagonal d.eigenvalues-b • outerSquare w).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, mul_sub, sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, hdiag, outerSquare_conjugate, w] using hconj
  have hw : ∑ i, w i^2 = 1 := by
    have h := orthogonal_dot d.orthogonal v v
    simpa only [dotProduct, ← pow_two, hv, U, w] using h
  obtain ⟨hsupport, hbound⟩ := harmonic_constraint_proved d.eigenvalues w b d.nonnegative hw hb hD
  have hUw : U *ᵥ w = v := by
    rw [show w = U.transpose*ᵥv from rfl, mulVec_mulVec, orthogonal_mul_transpose, one_mulVec]
  have hAU : A*U = U*diagonal d.eigenvalues := by
    calc
      _ = U * diagonal d.eigenvalues * (U.transpose*U) := by
        conv_lhs => lhs; rw [hA]
        simp only [spectralCombination, U, mul_assoc]
      _ = _ := by rw [orthogonal_transpose_mul d.orthogonal, mul_one]
  have hDy : diagonal d.eigenvalues *ᵥ (fun i => w i/d.eigenvalues i) = w := by
    ext i
    simp only [mulVec_diagonal]
    by_cases hi : d.eigenvalues i = 0
    · simp [hi, hsupport i hi]
    · field_simp
  refine ⟨⟨U*ᵥ(fun i => w i/d.eigenvalues i), ?_⟩, ?_⟩
  · change A *ᵥ (U*ᵥ(fun i => w i/d.eigenvalues i)) = v
    rw [mulVec_mulVec, hAU, ← mulVec_mulVec, hDy, hUw]
  · have hP : spectralPseudoinverse A = U * diagonal (fun i => (d.eigenvalues i)⁻¹) * U.transpose :=
      selected_cfc_eq d _
    have hquad : v ⬝ᵥ (spectralPseudoinverse A *ᵥ v) = ∑ i, w i^2/d.eigenvalues i := by
      rw [hP, ← mulVec_mulVec, ← mulVec_mulVec]
      change v ⬝ᵥ (U*ᵥ(diagonal (fun i => (d.eigenvalues i)⁻¹)*ᵥw)) = _
      have ht := dotProduct_transpose_mulVec U.transpose v
        (diagonal (fun i => (d.eigenvalues i)⁻¹)*ᵥw)
      rw [transpose_transpose] at ht
      rw [ht]
      change (diagonal (fun i => (d.eigenvalues i)⁻¹)*ᵥw) ⬝ᵥ w = _
      simp only [mulVec_diagonal, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rwa [hquad]

theorem harmonic_matrix_full {n : ℕ} (A : RealMatrix n)
    (v : Fin n → ℝ) (b : ℝ) (hv : ∑ i, v i^2 = 1) (hb : 0 < b)
    (horder : b • outerSquare v ≤ A) :
    IsMoorePenroseInverse A (spectralPseudoinverse A) ∧
      v ∈ Set.range (fun x : Fin n → ℝ => A *ᵥ x) ∧
      b * (v ⬝ᵥ (spectralPseudoinverse A *ᵥ v)) ≤ 1 := by
  have hout : (outerSquare v).PosSemidef := by
    change (vecMulVec v v).PosSemidef
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star v
  have hA : A.PosSemidef := ((hout.smul hb.le).nonneg.trans horder).posSemidef
  obtain ⟨d⟩ := orderedSpectral_exists_proved A hA
  exact ⟨spectralPseudoinverse_penrose d, harmonic_matrix d v b hv hb horder⟩

#print axioms harmonic_matrix
#print axioms harmonic_matrix_full

end NLA.RA09.Paper
