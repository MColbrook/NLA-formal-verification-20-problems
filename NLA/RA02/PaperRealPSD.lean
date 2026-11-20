module

public import NLA.RA02.PaperCholeskyExpectation

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical ComplexOrder
namespace NLA.RA02.Paper

theorem complexify_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) :
    complexify (A*B) = complexify A * complexify B := by
  ext i j
  simp [complexify, Matrix.mul_apply]

theorem complexify_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    complexify A.transpose = (complexify A).conjTranspose := by
  ext i j
  simp [complexify, Matrix.conjTranspose_apply]

theorem complexify_diagonal {n : ℕ} (d : Fin n → ℝ) :
    complexify (Matrix.diagonal d) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j
  by_cases h : i = j <;> simp [complexify, Matrix.diagonal_apply, h]

theorem complexify_posSemidef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    (complexify A).PosSemidef := by
  let h := hA.isHermitian
  have hspec : A = (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      Matrix.diagonal h.eigenvalues * (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ).transpose := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def] using h.spectral_theorem
  have he := congrArg complexify hspec
  rw [complexify_mul, complexify_mul, complexify_transpose, complexify_diagonal] at he
  rw [he]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (h.eigenvalues i : ℂ)
  exact Complex.nonneg_iff.mpr ⟨hA.eigenvalues_nonneg i, rfl⟩

theorem real_cholesky_expectation_determinant {k : ℕ} (A : Matrix (Fin (k+1)) (Fin (k+1)) ℝ)
    (hA : AllSquareMinorsNonzero A) (hpsd : A.PosSemidef) :
    NLA.RA02.expectedTrace (complexify A) k = A.det *
      ∑ h : Fin k ↪ Fin (k+1), (NLA.RA02.prefixTraceProduct (complexify A) (List.ofFn h))⁻¹ :=
  cholesky_expectation_determinant A hA (complexify_posSemidef A hpsd)

#print axioms real_cholesky_expectation_determinant
end NLA.RA02.Paper
