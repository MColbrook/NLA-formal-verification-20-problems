module

public import NLA.MD06.SpectralTraceBound.MatrixSpectral
public import NLA.MD06.SpectralTraceBound.ScalarEven

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.RootMD06PairingTrace
open Reference.RootMD06SpectralTrace Reference.MD06Nonbacktracking
open Reference.MD06CubicConfiguration
open Matrix
open scoped BigOperators

theorem actual_pairing_matching_transpose {n : ℕ} (p : Pairing n) :
    (MatchingMatrix p).transpose = MatchingMatrix p := by
  ext a b
  change (if p.val b = a then (1 : ℝ) else 0) = (if p.val a = b then 1 else 0)
  have h : p.val b = a ↔ p.val a = b := by
    constructor
    · intro h
      rw [← h, p.property.1]
    · intro h
      rw [← h, p.property.1]
  simp only [h]

theorem actual_pairing_adjacency_hermitian {n : ℕ} (p : Pairing n) :
    (AdjacencyMatrix p).IsHermitian := by
  have ht : (AdjacencyMatrix p).transpose = AdjacencyMatrix p := by
    unfold AdjacencyMatrix
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      actual_pairing_matching_transpose]
    exact (Matrix.mul_assoc _ _ _).symm
  change (AdjacencyMatrix p).conjTranspose = AdjacencyMatrix p
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using ht

theorem actual_pairing_adjacency_constant_action {n : ℕ} (p : Pairing n) :
    AdjacencyMatrix p *ᵥ (fun _ => (1 : ℝ)) = fun _ => 3 := by
  ext u
  simp only [Matrix.mulVec, dotProduct, actual_adjacency_port_sum, mul_one]
  rw [Finset.sum_comm]
  simp

theorem actual_hermitian_trace_polynomial_basis_action {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (i : Fin n) (t : ℕ) :
    (TracePolynomial A t).toEuclideanLin (hA.eigenvectorBasis i) =
      ScalarTracePolynomial (hA.eigenvalues i) t • hA.eigenvectorBasis i := by
  have hv : A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  induction t using Nat.twoStepInduction with
  | zero =>
    rw [actual_matrix_trace_polynomial_zero]
    simp [ScalarTracePolynomial, Matrix.toEuclideanLin, Matrix.toLpLin_one]
  | one =>
    rw [actual_matrix_trace_polynomial_one]
    exact hv
  | more t ht ht1 =>
    rw [actual_trace_polynomial_recurrence]
    simp only [Matrix.toEuclideanLin, map_sub, map_smul, Matrix.toLpLin_mul_same,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply, ht, ht1,
      map_smul, hv, ScalarTracePolynomial]
    module

theorem actual_hermitian_trace_polynomial_spectral_sum {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (t : ℕ) :
    Matrix.trace (TracePolynomial A t) =
      ∑ i : Fin n, ScalarTracePolynomial (hA.eigenvalues i) t := by
  classical
  rw [← Matrix.trace_toLin_eq _ (PiLp.basisFun 2 ℝ (Fin n)),
    LinearMap.trace_eq_matrix_trace ℝ hA.eigenvectorBasis.toBasis]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  change LinearMap.toMatrix hA.eigenvectorBasis.toBasis hA.eigenvectorBasis.toBasis
      ((TracePolynomial A t).toEuclideanLin) i i = _
  rw [LinearMap.toMatrix_apply]
  change hA.eigenvectorBasis.toBasis.repr
      ((TracePolynomial A t).toEuclideanLin (hA.eigenvectorBasis i)) i = _
  rw [actual_hermitian_trace_polynomial_basis_action]
  simp

theorem actual_pairing_adjacency_three_eigenvalue {n : ℕ} (p : Pairing n)
    (hn : 0 < n) (hA : (AdjacencyMatrix p).IsHermitian) :
    ∃ i : Fin n, hA.eigenvalues i = 3 := by
  let v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ))
  have hv : v ≠ 0 := by
    intro h
    have he := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x ⟨0, hn⟩) h
    norm_num [v] at he
  have he : Module.End.HasEigenvector (AdjacencyMatrix p).toEuclideanLin (3 : ℝ) v := by
    refine ⟨?_, hv⟩
    rw [Module.End.mem_eigenspace_iff]
    ext j
    change (AdjacencyMatrix p *ᵥ (fun _ => (1 : ℝ))) j = (3 : ℝ) * 1
    rw [actual_pairing_adjacency_constant_action]
    simp
  have hs : (3 : ℝ) ∈ spectrum ℝ (AdjacencyMatrix p) := by
    rw [← Matrix.spectrum_toLpLin 2]
    exact (Module.End.hasEigenvalue_of_hasEigenvector he).mem_spectrum
  rw [hA.spectrum_eq_image_range] at hs
  rcases hs with ⟨r, ⟨i, hi⟩, hr⟩
  refine ⟨i, ?_⟩
  change r = 3 at hr
  exact hi.trans hr

theorem actual_all_pairings_centered_even_trace_nonnegative {n : ℕ}
    (p : Pairing n) (hn : 0 < n) (m : ℕ) :
    0 ≤ Matrix.trace (NonbacktrackingMatrix p ^ (2 * m)) - (2 : ℝ) ^ (2 * m) +
      2 * n * (2 : ℝ) ^ m := by
  classical
  let hA := actual_pairing_adjacency_hermitian p
  obtain ⟨i, hi⟩ := actual_pairing_adjacency_three_eigenvalue p hn hA
  let f : Fin n → ℝ := fun j =>
    ScalarTracePolynomial (hA.eigenvalues j) (2 * m) + 2 * (2 : ℝ) ^ m
  have hf : ∀ j, 0 ≤ f j := by
    intro j
    dsimp [f]
    linarith [actual_scalar_even_uniform_lower_bound (hA.eigenvalues j) m]
  have hs : f i ≤ ∑ j : Fin n, f j :=
    Finset.single_le_sum (fun j _ => hf j) (Finset.mem_univ i)
  dsimp [f] at hs
  rw [hi, actual_scalar_three_value] at hs
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  rw [← actual_hermitian_trace_polynomial_spectral_sum] at hs
  have ht := (actual_nonbacktracking_trace_bounds p (2 * m)).1
  have hp : 0 ≤ (2 : ℝ) ^ m := by positivity
  nlinarith

#print axioms actual_pairing_matching_transpose
#print axioms actual_pairing_adjacency_hermitian
#print axioms actual_pairing_adjacency_constant_action
#print axioms actual_hermitian_trace_polynomial_basis_action
#print axioms actual_hermitian_trace_polynomial_spectral_sum
#print axioms actual_pairing_adjacency_three_eigenvalue
#print axioms actual_all_pairings_centered_even_trace_nonnegative

end Reference.RootMD06PairingTrace
