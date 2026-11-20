module

/- Complex-field adaptation of Paper/Pseudoinverse.lean, with Codex assistance. -/
public import NLA.RA09.ComplexHarmonicDefinitions
public import NLA.RA09.ComplexOverlapOrder

@[expose] public section

/-! The spectral inverse satisfies all four Moore–Penrose equations. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder
open Matrix
namespace NLA.RA09.ComplexPaper

theorem spectralCombination_mul {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) (u v : Fin n → ℝ) :
    spectralCombination d u * spectralCombination d v =
      spectralCombination d (fun i => u i * v i) := by
  let U : ComplexMatrix n := d.unitary
  calc
    _ = U * diagonal (fun i => (u i : ℂ)) * (U.conjTranspose*U) * diagonal (fun i => (v i : ℂ)) * U.conjTranspose := by
      simp only [spectralCombination, U, mul_assoc]
    _ = U * (diagonal (fun i => (u i : ℂ)) * diagonal (fun i => (v i : ℂ))) * U.conjTranspose := by
      rw [unitary_star_mul d.unitary]
      simp only [mul_one, mul_assoc]
    _ = _ := by
      rw [diagonal_mul_diagonal]
      simp only [spectralCombination, Complex.ofReal_mul, U]

theorem spectralPseudoinverse_penrose {n : ℕ} {A : ComplexMatrix n}
    (d : OrderedSpectralData A) : IsMoorePenroseInverse A (spectralPseudoinverse A) := by
  have hA : A = spectralCombination d d.eigenvalues := d.reconstruct
  have hP : spectralPseudoinverse A = spectralCombination d (fun i => (d.eigenvalues i)⁻¹) :=
    selected_cfc_eq d _
  have h : IsMoorePenroseInverse (spectralCombination d d.eigenvalues)
      (spectralCombination d (fun i => (d.eigenvalues i)⁻¹)) := by
    unfold IsMoorePenroseInverse
    simp only [spectralCombination_mul]
    refine ⟨?_, ?_, spectralCombination_hermitian d _, spectralCombination_hermitian d _⟩
    · apply congrArg (spectralCombination d)
      funext i
      by_cases hi : d.eigenvalues i = 0 <;> simp [hi]
    · apply congrArg (spectralCombination d)
      funext i
      by_cases hi : d.eigenvalues i = 0 <;> simp [hi]
  simpa only [← hA, ← hP] using h

#print axioms spectralPseudoinverse_penrose

end NLA.RA09.ComplexPaper
