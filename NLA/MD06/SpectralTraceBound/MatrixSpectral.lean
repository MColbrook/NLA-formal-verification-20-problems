module

public import NLA.MD06.SpectralTraceBound.ScalarRoots
public import NLA.MD06.SpectralTraceBound.ScalarEven
public import NLA.MD06.NonbacktrackingFoundation.TraceIdentity
public import NLA.MD06.NonbacktrackingFoundation.GraphMatrix
public import NLA.MD06.LaplacianSpectralGap.BottomKernel
public import Mathlib.LinearAlgebra.Trace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06SpectralTrace
open Reference.MD06Nonbacktracking Reference.MD06CubicConfiguration
open Reference.MD06Spectral Reference.MD06Correction
open scoped BigOperators

theorem actual_matrix_trace_polynomial_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    TracePolynomial A 0 = (2 : ℝ) • 1 := by
  simp [TracePolynomial, LiftCoefficients]

theorem actual_matrix_trace_polynomial_one {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    TracePolynomial A 1 = A := by
  simp only [TracePolynomial, LiftCoefficients, Matrix.mul_one, smul_zero,
    sub_zero]
  module

theorem actual_adjacency_laplacian_eigenbasis_action {n : ℕ}
    (p : SimpleConfiguration n) (i : Fin n) :
    (AdjacencyMatrix p.val).toEuclideanLin (LaplacianEigenbasis (configurationGraph p) i) =
      (3 - LaplacianEigenvalues (configurationGraph p) i) •
        LaplacianEigenbasis (configurationGraph p) i := by
  have h := actual_laplacian_basis_action (configurationGraph p) i
  unfold LaplacianOperator at h
  rw [actual_configuration_laplacian_matrix] at h
  simp only [map_sub, map_smul, Matrix.toLpLin_one,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
  calc
    (AdjacencyMatrix p.val).toEuclideanLin (LaplacianEigenbasis (configurationGraph p) i) =
      (3 : ℝ) • LaplacianEigenbasis (configurationGraph p) i -
        ((3 : ℝ) • LaplacianEigenbasis (configurationGraph p) i -
          (AdjacencyMatrix p.val).toEuclideanLin (LaplacianEigenbasis (configurationGraph p) i)) := by
            module
    _ = (3 : ℝ) • LaplacianEigenbasis (configurationGraph p) i -
        LaplacianEigenvalues (configurationGraph p) i •
          LaplacianEigenbasis (configurationGraph p) i := by rw [h]
    _ = _ := by rw [sub_smul]

theorem actual_matrix_trace_polynomial_eigenbasis_action {n : ℕ}
    (p : SimpleConfiguration n) (i : Fin n) (t : ℕ) :
    (TracePolynomial (AdjacencyMatrix p.val) t).toEuclideanLin
        (LaplacianEigenbasis (configurationGraph p) i) =
      ScalarTracePolynomial (3 - LaplacianEigenvalues (configurationGraph p) i) t •
        LaplacianEigenbasis (configurationGraph p) i := by
  induction t using Nat.twoStepInduction with
  | zero =>
    rw [actual_matrix_trace_polynomial_zero]
    simp [ScalarTracePolynomial, Matrix.toEuclideanLin, Matrix.toLpLin_one]
  | one =>
    rw [actual_matrix_trace_polynomial_one]
    exact actual_adjacency_laplacian_eigenbasis_action p i
  | more t ht ht1 =>
    rw [actual_trace_polynomial_recurrence]
    simp only [Matrix.toEuclideanLin, map_sub, map_smul, Matrix.toLpLin_mul_same,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, ht, ht1,
      map_smul, actual_adjacency_laplacian_eigenbasis_action, ScalarTracePolynomial]
    module

theorem actual_matrix_trace_polynomial_spectral_sum {n : ℕ}
    (p : SimpleConfiguration n) (t : ℕ) :
    Matrix.trace (TracePolynomial (AdjacencyMatrix p.val) t) =
      ∑ i : Fin n, ScalarTracePolynomial
        (3 - LaplacianEigenvalues (configurationGraph p) i) t := by
  classical
  rw [← Matrix.trace_toLin_eq _ (PiLp.basisFun 2 ℝ (Fin n)),
    LinearMap.trace_eq_matrix_trace ℝ (LaplacianEigenbasis (configurationGraph p)).toBasis]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change LinearMap.toMatrix (LaplacianEigenbasis (configurationGraph p)).toBasis
      (LaplacianEigenbasis (configurationGraph p)).toBasis
      ((TracePolynomial (AdjacencyMatrix p.val) t).toEuclideanLin) i i = _
  rw [LinearMap.toMatrix_apply]
  change (LaplacianEigenbasis (configurationGraph p)).toBasis.repr
      ((TracePolynomial (AdjacencyMatrix p.val) t).toEuclideanLin
        (LaplacianEigenbasis (configurationGraph p) i)) i = _
  rw [actual_matrix_trace_polynomial_eigenbasis_action]
  simp

#print axioms actual_matrix_trace_polynomial_zero
#print axioms actual_matrix_trace_polynomial_one
#print axioms actual_adjacency_laplacian_eigenbasis_action
#print axioms actual_matrix_trace_polynomial_eigenbasis_action
#print axioms actual_matrix_trace_polynomial_spectral_sum

end Reference.RootMD06SpectralTrace
