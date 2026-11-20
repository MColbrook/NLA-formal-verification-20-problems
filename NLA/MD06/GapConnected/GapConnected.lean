module

public import NLA.MD06.LaplacianSpectralGap.BottomKernel
public import NLA.MD06.RadiusEmbedding.PaperSpectrumDefinitions
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06GapConnected
open Reference.MD06Correction Reference.MD06Spectral Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_laplacian_kernel_finrank_bridge {n : ℕ} (G : SimpleGraph (Fin n)) :
    Module.finrank ℝ (LaplacianOperator G).ker =
      Module.finrank ℝ (G.lapMatrix ℝ).toLin'.ker := by
  classical
  let e : (LaplacianOperator G).ker ≃ₗ[ℝ] (G.lapMatrix ℝ).toLin'.ker :=
    { toFun := fun x => ⟨fun i => x.val i, by
        apply LinearMap.mem_ker.mpr
        ext i
        change ((G.lapMatrix ℝ) *ᵥ (fun j => x.val j)) i = 0
        exact congrArg (fun z : Configuration n => z i) (LinearMap.mem_ker.mp x.property)⟩
      invFun := fun x => ⟨WithLp.toLp 2 x.val, by
        apply LinearMap.mem_ker.mpr
        ext i
        change ((G.lapMatrix ℝ) *ᵥ x.val) i = 0
        exact congrFun (LinearMap.mem_ker.mp x.property) i⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
      map_add' := by intro x y; apply Subtype.ext; rfl
      map_smul' := by intro a x; apply Subtype.ext; rfl }
  exact e.finrank_eq

theorem actual_positive_gap_zero_spectrum_singleton {n : ℕ}
    (G : SimpleGraph (Fin n)) (hn : 2 ≤ n) (hp : 0 < LaplacianGap G hn) :
    (Finset.univ.filter fun i => LaplacianEigenvalues G i = 0) =
      {⟨n-1, by omega⟩} := by
  classical
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hi
    apply Fin.ext
    by_contra hne
    change i.val ≠ n-1 at hne
    have hle : i ≤ (⟨n-2, by omega⟩ : Fin n) := by
      change i.val ≤ n-2
      have := i.isLt
      omega
    have hh := actual_laplacian_eigenvalues_antitone G hle
    unfold LaplacianGap at hp
    rw [hi] at hh
    linarith
  · intro hi
    subst i
    exact actual_laplacian_bottom_eigenvalue_zero G (by omega)

theorem actual_positive_gap_kernel_finrank_one {n : ℕ}
    (G : SimpleGraph (Fin n)) (hn : 2 ≤ n) (hp : 0 < LaplacianGap G hn) :
    Module.finrank ℝ (LaplacianOperator G).ker = 1 := by
  classical
  have hd : Module.finrank ℝ (Configuration n) = n := by simp [Configuration]
  have hc := (LaplacianSymmetric G).card_filter_eigenvalues_eq hd (0 : ℝ)
  change (Finset.univ.filter fun i => LaplacianEigenvalues G i = 0).card =
    Module.finrank ℝ (Module.End.eigenspace (LaplacianOperator G) 0) at hc
  rw [Module.End.eigenspace_zero] at hc
  rw [actual_positive_gap_zero_spectrum_singleton G hn hp, Finset.card_singleton] at hc
  exact hc.symm

theorem actual_positive_gap_connected {n : ℕ}
    (G : SimpleGraph (Fin n)) (hn : 2 ≤ n) (hp : 0 < LaplacianGap G hn) :
    G.Connected := by
  classical
  have hcard : Fintype.card G.ConnectedComponent = 1 := by
    rw [G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix,
      ← actual_laplacian_kernel_finrank_bridge G,
      actual_positive_gap_kernel_finrank_one G hn hp]
  have hs : Subsingleton G.ConnectedComponent := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  apply (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
  refine ⟨⟨0, by omega⟩, ?_⟩
  intro v
  exact SimpleGraph.ConnectedComponent.eq.mp (hs.elim _ _)

theorem actual_positive_total_gap_connected {n : ℕ}
    (G : SimpleGraph (Fin n))
    (hp : 0 < Reference.MD06RadiusEmbedding.TotalLaplacianGap G) :
    G.Connected := by
  classical
  unfold Reference.MD06RadiusEmbedding.TotalLaplacianGap at hp
  split_ifs at hp with hn
  · exact actual_positive_gap_connected G hn hp
  · linarith

#print axioms actual_laplacian_kernel_finrank_bridge
#print axioms actual_positive_gap_zero_spectrum_singleton
#print axioms actual_positive_gap_kernel_finrank_one
#print axioms actual_positive_gap_connected
#print axioms actual_positive_total_gap_connected
end Reference.MD06GapConnected
