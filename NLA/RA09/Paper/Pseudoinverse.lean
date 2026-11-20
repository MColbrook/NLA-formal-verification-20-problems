module

public import NLA.RA09.PaperHarmonicDefinitions
public import NLA.RA09.OverlapOrder

@[expose] public section

/-! The spectral inverse satisfies all four Moore–Penrose equations. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical MatrixOrder
open Matrix
namespace NLA.RA09.Paper

theorem spectralCombination_mul {n : ℕ} {A : RealMatrix n}
    (d : OrderedSpectralData A) (u v : Fin n → ℝ) :
    spectralCombination d u * spectralCombination d v =
      spectralCombination d (fun i => u i * v i) := by
  let U : RealMatrix n := d.orthogonal
  calc
    _ = U * diagonal u * (U.transpose*U) * diagonal v * U.transpose := by
      simp only [spectralCombination, U, mul_assoc]
    _ = U * (diagonal u * diagonal v) * U.transpose := by
      rw [orthogonal_transpose_mul d.orthogonal]
      simp only [mul_one, mul_assoc]
    _ = _ := by rw [diagonal_mul_diagonal]; rfl

theorem spectralPseudoinverse_penrose {n : ℕ} {A : RealMatrix n}
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

end NLA.RA09.Paper
