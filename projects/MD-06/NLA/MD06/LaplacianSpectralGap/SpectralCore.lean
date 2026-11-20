module

public import NLA.MD06.LaplacianSpectralGap.Definitions
public import NLA.MD06.GraphCriticalityHessian.Laplacian

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Spectral
open Reference.MD06Correction Reference.MD06Actual Matrix
open scoped BigOperators

theorem actual_laplacian_operator_quadratic {n : ℕ} (G : SimpleGraph (Fin n)) (z : Configuration n) :
    inner ℝ z (LaplacianOperator G z) = LaplacianQuadratic G (fun i => z i) := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold LaplacianOperator
  simp only [star_trivial]
  change ((G.lapMatrix ℝ) *ᵥ (fun i => z i)) ⬝ᵥ (fun i => z i) = _
  rw [dotProduct_comm]
  exact actual_laplacian_quadratic_identity G _

theorem actual_laplacian_eigenvalues_antitone {n : ℕ} (G : SimpleGraph (Fin n)) :
    Antitone (LaplacianEigenvalues G) := (LaplacianSymmetric G).eigenvalues_antitone _

theorem actual_laplacian_basis_action {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    LaplacianOperator G (LaplacianEigenbasis G i) =
      LaplacianEigenvalues G i • LaplacianEigenbasis G i :=
  (LaplacianSymmetric G).apply_eigenvectorBasis _ i

theorem actual_laplacian_eigenvalue_quadratic {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    LaplacianQuadratic G (fun j => LaplacianEigenbasis G i j) = LaplacianEigenvalues G i := by
  rw [← actual_laplacian_operator_quadratic,actual_laplacian_basis_action,
    real_inner_smul_right,real_inner_self_eq_norm_sq]
  simp only [(LaplacianEigenbasis G).orthonormal.1 i,one_pow,mul_one]

theorem actual_laplacian_eigenvalues_nonnegative {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    0 ≤ LaplacianEigenvalues G i := by
  classical
  rw [← actual_laplacian_eigenvalue_quadratic]
  unfold LaplacianQuadratic
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro k _
  split_ifs
  · exact sq_nonneg _
  · exact le_refl _

theorem actual_laplacian_repr_action {n : ℕ} (G : SimpleGraph (Fin n)) (z : Configuration n) (i : Fin n) :
    (LaplacianEigenbasis G).repr (LaplacianOperator G z) i =
      LaplacianEigenvalues G i * (LaplacianEigenbasis G).repr z i :=
  (LaplacianSymmetric G).eigenvectorBasis_apply_self_apply _ z i

theorem actual_laplacian_diagonal_quadratic {n : ℕ} (G : SimpleGraph (Fin n)) (z : Configuration n) :
    LaplacianQuadratic G (fun i => z i) =
      ∑ i, LaplacianEigenvalues G i * ((LaplacianEigenbasis G).repr z i)^2 := by
  rw [← actual_laplacian_operator_quadratic,
    ← (LaplacianEigenbasis G).repr.inner_map_map z (LaplacianOperator G z),PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change ((LaplacianEigenbasis G).repr (LaplacianOperator G z) i)*
    ((LaplacianEigenbasis G).repr z i) = _
  rw [actual_laplacian_repr_action]
  ring

#print axioms actual_laplacian_operator_quadratic
#print axioms actual_laplacian_eigenvalues_antitone
#print axioms actual_laplacian_basis_action
#print axioms actual_laplacian_eigenvalue_quadratic
#print axioms actual_laplacian_eigenvalues_nonnegative
#print axioms actual_laplacian_repr_action
#print axioms actual_laplacian_diagonal_quadratic
end Reference.MD06Spectral
