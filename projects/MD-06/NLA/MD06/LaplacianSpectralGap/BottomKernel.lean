module

public import NLA.MD06.LaplacianSpectralGap.SpectralCore

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Spectral
open Reference.MD06Correction Reference.MD06Actual Matrix WithLp
open scoped BigOperators

theorem actual_laplacian_zero_eigenvalue_exists {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) :
    ∃ i : Fin n, LaplacianEigenvalues G i = 0 := by
  classical
  let v : Configuration n := toLp 2 (fun _ => (1 : ℝ))
  have hv : v ≠ 0 := by
    intro h
    have he := congrArg (fun x : Configuration n => x ⟨0,hn⟩) h
    norm_num [v] at he
  have hl : LaplacianOperator G v = 0 := by
    ext i
    change ((G.lapMatrix ℝ) *ᵥ (fun _ => (1 : ℝ))) i = 0
    exact congrFun (G.lapMatrix_mulVec_one_eq_zero ℝ) i
  have he : Module.End.HasEigenvector (LaplacianOperator G) (0 : ℝ) v := by
    refine ⟨?_,hv⟩
    rw [Module.End.mem_eigenspace_iff]
    simpa only [zero_smul] using hl
  exact (LaplacianSymmetric G).exists_eigenvalues_eq _ (Module.End.hasEigenvalue_of_hasEigenvector he)

theorem actual_laplacian_bottom_eigenvalue_zero {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) :
    LaplacianEigenvalues G ⟨n-1,by omega⟩ = 0 := by
  obtain ⟨i,hi⟩ := actual_laplacian_zero_eigenvalue_exists G hn
  have hj : i ≤ (⟨n-1,by omega⟩ : Fin n) := by change i.val ≤ n-1;omega
  have hl := actual_laplacian_eigenvalues_antitone G hj
  have hp := actual_laplacian_eigenvalues_nonnegative G (⟨n-1,by omega⟩ : Fin n)
  linarith

theorem actual_connected_bottom_basis_constant {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 0 < n) :
    ∀ i j : Fin n, LaplacianEigenbasis G ⟨n-1,by omega⟩ i =
      LaplacianEigenbasis G ⟨n-1,by omega⟩ j := by
  classical
  have hq := actual_laplacian_eigenvalue_quadratic G (⟨n-1,by omega⟩ : Fin n)
  rw [actual_laplacian_bottom_eigenvalue_zero G hn] at hq
  have hb : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ)
      (fun i => LaplacianEigenbasis G ⟨n-1,by omega⟩ i)
      (fun i => LaplacianEigenbasis G ⟨n-1,by omega⟩ i) = 0 := by
    rw [Matrix.toLinearMap₂'_apply',actual_laplacian_quadratic_identity,hq]
  have he := (SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable ℝ G _).mp hb
  exact fun i j => he i j (hg i j)

theorem actual_connected_bottom_basis_coordinate_nonzero {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 0 < n) (i : Fin n) :
    LaplacianEigenbasis G ⟨n-1,by omega⟩ i ≠ 0 := by
  intro h
  have he : LaplacianEigenbasis G ⟨n-1,by omega⟩ = 0 := by
    ext j
    change LaplacianEigenbasis G ⟨n-1,by omega⟩ j = 0
    rw [actual_connected_bottom_basis_constant G hg hn j i,h]
  exact (LaplacianEigenbasis G).orthonormal.ne_zero ⟨n-1,by omega⟩ he

theorem actual_connected_bottom_repr_coordinate_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 0 < n) (z : Configuration n) :
    (LaplacianEigenbasis G).repr z ⟨n-1,by omega⟩ =
      LaplacianEigenbasis G ⟨n-1,by omega⟩ ⟨0,hn⟩ * (∑ i, z i) := by
  rw [(LaplacianEigenbasis G).repr_apply_apply,PiLp.inner_apply]
  change (∑ j, z j*LaplacianEigenbasis G ⟨n-1,by omega⟩ j) = _
  simp_rw [actual_connected_bottom_basis_constant G hg hn _ ⟨0,hn⟩]
  rw [← Finset.sum_mul,mul_comm]

theorem actual_connected_bottom_repr_zero_iff_mean_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 0 < n) (z : Configuration n) :
    (LaplacianEigenbasis G).repr z ⟨n-1,by omega⟩ = 0 ↔ (∑ i, z i) = 0 := by
  rw [actual_connected_bottom_repr_coordinate_sum G hg hn z]
  simp only [mul_eq_zero,actual_connected_bottom_basis_coordinate_nonzero G hg hn ⟨0,hn⟩,
    false_or]

theorem actual_connected_other_eigenbasis_mean_zero {n : ℕ} (G : SimpleGraph (Fin n))
    (hg : G.Connected) (hn : 0 < n) (i : Fin n) (hi : i ≠ ⟨n-1,by omega⟩) :
    (∑ j, LaplacianEigenbasis G i j) = 0 := by
  apply (actual_connected_bottom_repr_zero_iff_mean_zero G hg hn (LaplacianEigenbasis G i)).mp
  rw [(LaplacianEigenbasis G).repr_self]
  simp [Ne.symm hi]

#print axioms actual_laplacian_zero_eigenvalue_exists
#print axioms actual_laplacian_bottom_eigenvalue_zero
#print axioms actual_connected_bottom_basis_constant
#print axioms actual_connected_bottom_basis_coordinate_nonzero
#print axioms actual_connected_bottom_repr_coordinate_sum
#print axioms actual_connected_bottom_repr_zero_iff_mean_zero
#print axioms actual_connected_other_eigenbasis_mean_zero
end Reference.MD06Spectral
