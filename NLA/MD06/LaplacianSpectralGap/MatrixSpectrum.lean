module

public import NLA.MD06.LaplacianSpectralGap.SpectralCore

@[expose] public section
set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Reference.MD06Spectral

theorem actual_laplacian_sorted_eigenvalue_mem_matrix_spectrum {n : ℕ}
    (G : SimpleGraph (Fin n)) (i : Fin n) :
    LaplacianEigenvalues G i ∈ spectrum ℝ (G.lapMatrix ℝ) := by
  classical
  rw [← Matrix.spectrum_toLpLin 2]
  exact ((LaplacianSymmetric G).hasEigenvalue_eigenvalues _ i).mem_spectrum

#print axioms actual_laplacian_sorted_eigenvalue_mem_matrix_spectrum
end Reference.MD06Spectral
