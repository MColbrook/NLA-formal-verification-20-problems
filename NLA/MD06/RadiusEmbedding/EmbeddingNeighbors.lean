module

public import NLA.MD06.RadiusEmbedding.NeighborCounts

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Reference.MD06RadiusEmbedding
open SimpleGraph
open Reference.MD06CleanCycle
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem actual_radius_tree_neighbors_adj {v : V} (c : G.Walk v v) (hc0 : c.IsCycle)
    (R : ℕ) (hR : 4 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x y : TreeNodes c.length R) (hy : y ∈ TreeNeighbors hR x) :
    G.Adj (ActualRadiusNodes c R (by omega) hc hcubic x)
      (ActualRadiusNodes c R (by omega) hc hcubic y) := by
  by_cases h0 : x.1.val = 0
  · simp only [TreeNeighbors,dif_pos h0,Finset.mem_insert,Finset.mem_singleton] at hy
    have hxroot := actual_tree_node_zero_eq_root x h0
    rcases hy with rfl | rfl | rfl
    · rw [hxroot]
      exact actual_radius_nodes_nextroot_adj c hc0 R (by omega) hc hcubic _
    · rw [hxroot]
      exact actual_radius_nodes_previousroot_adj c hc0 R (by omega) hc hcubic _
    · exact (deleteEdges_adj.mp (actual_radius_tree_child_zero_adj c R (by omega) hc hcubic x
        (by omega))).1
  · by_cases hx : x.1.val < R
    · simp only [TreeNeighbors,dif_neg h0,dif_pos hx,Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact (deleteEdges_adj.mp (actual_radius_tree_parent_adj c R (by omega) hc hcubic x
          (by omega))).1.symm
      · exact (deleteEdges_adj.mp (actual_radius_tree_child_zero_adj c R (by omega) hc hcubic x hx)).1
      · exact (deleteEdges_adj.mp (actual_radius_tree_child_one_adj c R (by omega) hc hcubic x
          (by omega) hx)).1
    · simp only [TreeNeighbors,dif_neg h0,dif_neg hx,Finset.mem_singleton] at hy
      subst y
      exact (deleteEdges_adj.mp (actual_radius_tree_parent_adj c R (by omega) hc hcubic x
        (by omega))).1.symm

theorem actual_radius_tree_neighbors_image_subset {v : V} (c : G.Walk v v) (hc0 : c.IsCycle)
    (R : ℕ) (hR : 4 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x : TreeNodes c.length R) :
    (TreeNeighbors hR x).image (ActualRadiusNodes c R (by omega) hc hcubic) ⊆
      G.neighborFinset (ActualRadiusNodes c R (by omega) hc hcubic x) := by
  intro y hy
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hy
  exact (G.mem_neighborFinset _ _).mpr (actual_radius_tree_neighbors_adj c hc0 R hR hc hcubic x a ha)

theorem actual_radius_tree_induced_neighbors {v : V} (c : G.Walk v v) (hc0 : c.IsCycle)
    (R : ℕ) (hR : 4 ≤ R) (hell : 4 ≤ c.length)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x : TreeNodes c.length R) :
    G.neighborFinset (ActualRadiusNodes c R (by omega) hc hcubic x) ∩
        Finset.univ.image (ActualRadiusNodes c R (by omega) hc hcubic) =
      (TreeNeighbors hR x).image (ActualRadiusNodes c R (by omega) hc hcubic) := by
  have hs := actual_radius_tree_neighbors_image_subset c hc0 R hR hc hcubic x
  by_cases hx : x.1.val < R
  · have he : (TreeNeighbors hR x).image (ActualRadiusNodes c R (by omega) hc hcubic) =
        G.neighborFinset (ActualRadiusNodes c R (by omega) hc hcubic x) := by
      apply Finset.eq_of_subset_of_card_le hs
      rw [Finset.card_image_of_injective _ (ActualRadiusNodes c R (by omega) hc hcubic).injective,
        actual_tree_neighbors_card_interior hell hR x hx,card_neighborFinset_eq_degree]
      exact le_of_eq (hcubic _)
    rw [← he]
    exact Finset.inter_eq_left.mpr (Finset.image_subset_image (Finset.subset_univ _))
  · have hdepth : x.1.val = R := by have h := x.1.isLt; omega
    have h0 : x.1.val ≠ 0 := by omega
    apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨hzn,hzim⟩ := Finset.mem_inter.mp hz
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hzim
      have he := actual_radius_tree_boundary_neighbor_parent c R (by omega) hc hcubic
        x y hdepth ((G.mem_neighborFinset _ _).mp hzn)
      subst y
      apply Finset.mem_image.mpr
      refine ⟨ParentNode x (by omega),?_,rfl⟩
      simp only [TreeNeighbors,dif_neg h0,dif_neg hx,Finset.mem_singleton]
    · exact Finset.subset_inter hs (Finset.image_subset_image (Finset.subset_univ _))

noncomputable def ActualCleanCycleEmbedding {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n}
    (c : G.Walk v v) (hc0 : c.IsCycle) (R : ℕ) (hR : 4 ≤ R) (hell : 4 ≤ c.length)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3) : CleanCycleEmbedding (ell := c.length) G hR where
  nodes := ActualRadiusNodes c R (by omega) hc hcubic
  induced_neighbors := actual_radius_tree_induced_neighbors c hc0 R hR hell hc hcubic
  closed_interior := actual_radius_nodes_closed_interior c R (by omega) hc hcubic

theorem actual_clean_radius_embedding_exists {n : ℕ} {G : SimpleGraph (Fin n)} {v : Fin n}
    (c : G.Walk v v) (hc0 : c.IsCycle) (R : ℕ) (hR : 4 ≤ R) (hell : 4 ≤ c.length)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3) :
    Nonempty (CleanCycleEmbedding (ell := c.length) G hR) :=
  ⟨ActualCleanCycleEmbedding c hc0 R hR hell hc hcubic⟩

end Reference.MD06RadiusEmbedding
