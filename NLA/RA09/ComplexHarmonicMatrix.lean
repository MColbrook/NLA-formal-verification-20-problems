module

/- Complex-field adaptation of Paper/HarmonicMatrix.lean, with Codex assistance. -/
public import NLA.RA09.ComplexPseudoinverse
public import NLA.RA09.ComplexOrderedExistence

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder ComplexOrder
open Matrix
namespace NLA.RA09.ComplexPaper

theorem harmonic_matrix {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A)
    (v : Fin n → ℂ) (b : ℝ) (hb : 0 < b)
    (horder : (b : ℂ) • outerSquare v ≤ A) :
    v ∈ Set.range (fun x : Fin n → ℂ => A *ᵥ x) ∧
      (b : ℂ) * (star v ⬝ᵥ (spectralPseudoinverse A *ᵥ v)) ≤ 1 := by
  let U : ComplexMatrix n := d.unitary
  let w : Fin n → ℂ := U.conjTranspose *ᵥ v
  have hA : A = spectralCombination d d.eigenvalues := d.reconstruct
  have hdiag : U.conjTranspose*A*U = diagonal (fun i => (d.eigenvalues i : ℂ)) := by
    exact (congrArg (fun M : ComplexMatrix n => U.conjTranspose*M*U) d.reconstruct).trans
      (spectralCombination_conjugate d d.eigenvalues)
  have hconj := (sub_nonneg.mpr horder).posSemidef.conjTranspose_mul_mul_same U
  have hD : (diagonal (fun i => (d.eigenvalues i : ℂ))-(b : ℂ) • outerSquare w).PosSemidef := by
    simpa only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      hdiag, outerSquare_conjugate, w] using hconj
  obtain ⟨hsupport, hbound⟩ := harmonic_constraint_proved d.eigenvalues w b d.nonnegative hb hD
  have hUw : U *ᵥ w = v := by
    rw [show w = U.conjTranspose*ᵥv from rfl, mulVec_mulVec, unitary_mul_star, one_mulVec]
  have hAU : A*U = U*diagonal (fun i => (d.eigenvalues i : ℂ)) := by
    calc
      _ = U * diagonal (fun i => (d.eigenvalues i : ℂ)) * (U.conjTranspose*U) := by
        conv_lhs => lhs; rw [hA]
        simp only [spectralCombination, U, mul_assoc]
      _ = _ := by rw [unitary_star_mul d.unitary, mul_one]
  have hDy : diagonal (fun i => (d.eigenvalues i : ℂ)) *ᵥ
      (fun i => w i/(d.eigenvalues i : ℂ)) = w := by
    ext i
    simp only [mulVec_diagonal]
    by_cases hi : d.eigenvalues i = 0
    · simp [hi, hsupport i hi]
    · have hic : (d.eigenvalues i : ℂ) ≠ 0 := by exact_mod_cast hi
      field_simp
  refine ⟨⟨U*ᵥ(fun i => w i/(d.eigenvalues i : ℂ)), ?_⟩, ?_⟩
  · change A *ᵥ (U*ᵥ(fun i => w i/(d.eigenvalues i : ℂ))) = v
    rw [mulVec_mulVec, hAU, ← mulVec_mulVec, hDy, hUw]
  · have hP : spectralPseudoinverse A = U *
        diagonal (fun i => (d.eigenvalues i : ℂ)⁻¹) * U.conjTranspose := by
      simpa only [spectralPseudoinverse, spectralCombination, U, Complex.ofReal_inv] using
        selected_cfc_eq d (fun x => x⁻¹)
    have hquad : star v ⬝ᵥ (spectralPseudoinverse A *ᵥ v) =
        ((∑ i, Complex.normSq (w i)/d.eigenvalues i : ℝ) : ℂ) := by
      rw [hP, ← mulVec_mulVec, ← mulVec_mulVec]
      change star v ⬝ᵥ (U*ᵥ(diagonal (fun i => ((d.eigenvalues i)⁻¹ : ℂ))*ᵥw)) = _
      have hwstar : star w = star v ᵥ* U := by
        simp only [w, star_mulVec, conjTranspose_conjTranspose]
      rw [dotProduct_mulVec, ← hwstar]
      change star w ⬝ᵥ (diagonal (fun i => ((d.eigenvalues i)⁻¹ : ℂ))*ᵥw) = _
      simp only [mulVec_diagonal, dotProduct, Complex.ofReal_sum, Complex.ofReal_div,
        Complex.normSq_eq_conj_mul_self, Pi.star_apply, Complex.star_def, Complex.ofReal_inv]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hquad]
    exact_mod_cast hbound

theorem harmonic_matrix_full {n : ℕ} (A : ComplexMatrix n)
    (v : Fin n → ℂ) (b : ℝ) (hb : 0 < b)
    (horder : (b : ℂ) • outerSquare v ≤ A) :
    IsMoorePenroseInverse A (spectralPseudoinverse A) ∧
      v ∈ Set.range (fun x : Fin n → ℂ => A *ᵥ x) ∧
      (b : ℂ) * (star v ⬝ᵥ (spectralPseudoinverse A *ᵥ v)) ≤ 1 := by
  have hout : (outerSquare v).PosSemidef := posSemidef_vecMulVec_self_star v
  have hb' : (0 : ℂ) ≤ (b : ℂ) := by exact_mod_cast hb.le
  have hA : A.PosSemidef := ((hout.smul hb').nonneg.trans horder).posSemidef
  obtain ⟨d⟩ := orderedSpectral_exists_proved A hA
  exact ⟨spectralPseudoinverse_penrose d, harmonic_matrix d v b hb horder⟩

#print axioms harmonic_matrix_full
end NLA.RA09.ComplexPaper
