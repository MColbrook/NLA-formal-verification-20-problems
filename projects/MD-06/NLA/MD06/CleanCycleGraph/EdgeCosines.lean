module

public import NLA.MD06.CleanCycleGraph.ResidualNorm

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile
attribute [local instance] Classical.propDecidable

theorem actual_profile_margin_le_one : Real.sqrt (1-(Root 4)^2) ≤ 1 := by
  have hr := actual_root_interval (by omega : 4 ≤ 4)
  have hs := Real.sq_sqrt (show 0 ≤ 1-(Root 4)^2 by nlinarith [hr.1,hr.2])
  have hp := Real.sqrt_nonneg (1-(Root 4)^2)
  nlinarith [sq_nonneg (Root 4)]

theorem actual_any_root_pair_cosine {ell R : ℕ} (hR : 4 ≤ R) (i j : Fin ell) :
    Real.sqrt (1-(Root 4)^2) ≤ Real.cos (NodeProfile (RootNode (R := R) i)-
      NodeProfile (RootNode (R := R) j)) := by
  have hc : Real.cos (Height R (Root R) 0*2) = Real.sqrt (1-(Root R)^2) := by
    simpa [mul_comm] using actual_opposite_root_cosine hR
  simp only [NodeProfile,RootNode]
  unfold RootSign
  split_ifs <;> ring_nf
  all_goals try simp
  all_goals
    first
    | exact actual_profile_margin_le_one
    | exact sq_nonneg _
    | rw [hc]
      exact actual_root_uniform_cosine hR

theorem actual_child_zero_cosine {ell R : ℕ} (hR : 4 ≤ R) (x : TreeNodes ell R)
    (hx : x.1.val < R) : Real.sqrt (1-(Root 4)^2) ≤
      Real.cos (NodeProfile x-NodeProfile (ChildZero x hx)) := by
  change _ ≤ Real.cos (RootSign x.2.1*Height R (Root R) x.1.val -
    RootSign x.2.1*Height R (Root R) (x.1.val+1))
  rw [←mul_sub,actual_height_step hx,actual_root_sign_cosine]
  exact actual_delta_cosine_uniform hR x.1.val

theorem actual_child_one_cosine {ell R : ℕ} (hR : 4 ≤ R) (x : TreeNodes ell R)
    (h0 : 0 < x.1.val) (hx : x.1.val < R) : Real.sqrt (1-(Root 4)^2) ≤
      Real.cos (NodeProfile x-NodeProfile (ChildOne x h0 hx)) := by
  change _ ≤ Real.cos (RootSign x.2.1*Height R (Root R) x.1.val -
    RootSign x.2.1*Height R (Root R) (x.1.val+1))
  rw [←mul_sub,actual_height_step hx,actual_root_sign_cosine]
  exact actual_delta_cosine_uniform hR x.1.val

theorem actual_parent_cosine {ell R : ℕ} (hR : 4 ≤ R) (x : TreeNodes ell R)
    (h0 : 0 < x.1.val) : Real.sqrt (1-(Root 4)^2) ≤
      Real.cos (NodeProfile x-NodeProfile (ParentNode x h0)) := by
  change _ ≤ Real.cos (RootSign x.2.1*Height R (Root R) x.1.val -
    RootSign x.2.1*Height R (Root R) (x.1.val-1))
  have hle := x.1.isLt
  have hj : x.1.val-1 < R := by omega
  have he : x.1.val-1+1 = x.1.val := by omega
  have hs := actual_height_step hj (Root R)
  rw [he] at hs
  have hr : Height R (Root R) x.1.val - Height R (Root R) (x.1.val-1) =
      -Delta (Root R) (x.1.val-1) := by linarith
  rw [←mul_sub,hr,mul_neg,Real.cos_neg,actual_root_sign_cosine]
  exact actual_delta_cosine_uniform hR (x.1.val-1)

theorem actual_tree_neighbor_cosine {ell R : ℕ} (hR : 4 ≤ R) (x y : TreeNodes ell R)
    (hy : y ∈ TreeNeighbors hR x) : Real.sqrt (1-(Root 4)^2) ≤ Real.cos (NodeProfile x-NodeProfile y) := by
  by_cases h0 : x.1.val = 0
  · simp only [TreeNeighbors,dif_pos h0,Finset.mem_insert,Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · rw [actual_node_root_form x h0]
      exact actual_any_root_pair_cosine hR _ _
    · rw [actual_node_root_form x h0]
      exact actual_any_root_pair_cosine hR _ _
    · exact actual_child_zero_cosine hR x (by omega)
  · have hp : 0 < x.1.val := by omega
    by_cases hx : x.1.val < R
    · simp only [TreeNeighbors,dif_neg h0,dif_pos hx,Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact actual_parent_cosine hR x hp
      · exact actual_child_zero_cosine hR x hx
      · exact actual_child_one_cosine hR x hp hx
    · simp only [TreeNeighbors,dif_neg h0,dif_neg hx,Finset.mem_singleton] at hy
      subst y
      exact actual_parent_cosine hR x hp

theorem actual_inside_outside_edge_profiles_zero {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hR : 4 ≤ R) (e : CleanCycleEmbedding (ell := ell) G hR)
    (x : TreeNodes ell R) (v : Fin n) (hv : v ∉ Set.range e.nodes) (hadj : G.Adj (e.nodes x) v) :
    EmbeddedProfile e.nodes (e.nodes x) = 0 ∧ EmbeddedProfile e.nodes v = 0 := by
  have hx : x.1.val = R := by
    have hle := x.1.isLt
    by_contra hh
    have hlt : x.1.val < R := by omega
    have him := e.closed_interior x hlt ((G.mem_neighborFinset (e.nodes x) v).mpr hadj)
    obtain ⟨y,hy,hey⟩ := Finset.mem_image.mp him
    exact hv ⟨y,hey⟩
  exact ⟨actual_embedded_leaf_profile_zero e.nodes x hx,actual_embedded_profile_outside e.nodes v hv⟩

theorem actual_embedded_all_edge_cosines {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hR : 4 ≤ R) (e : CleanCycleEmbedding (ell := ell) G hR) :
    ∀ i j, G.Adj i j → Real.sqrt (1-(Root 4)^2) ≤ Real.cos (EmbeddedProfile e.nodes i-EmbeddedProfile e.nodes j) := by
  intro i j hadj
  by_cases hi : i ∈ Set.range e.nodes
  · obtain ⟨x,hx⟩ := hi
    by_cases hj : j ∈ Set.range e.nodes
    · obtain ⟨y,hy⟩ := hj
      have hm : e.nodes y ∈ G.neighborFinset (e.nodes x) ∩ Finset.univ.image e.nodes := by
        apply Finset.mem_inter.mpr
        refine ⟨(G.mem_neighborFinset _ _).mpr (by rwa [hx,hy]),?_⟩
        exact Finset.mem_image.mpr ⟨y,Finset.mem_univ y,rfl⟩
      rw [e.induced_neighbors x] at hm
      obtain ⟨z,hz,hez⟩ := Finset.mem_image.mp hm
      have he : z = y := e.nodes.injective hez
      subst z
      rw [←hx,←hy,actual_embedded_profile_at_node,actual_embedded_profile_at_node]
      exact actual_tree_neighbor_cosine hR x y hz
    · have hz := actual_inside_outside_edge_profiles_zero G hR e x j hj (by rwa [hx])
      rw [←hx,hz.1,hz.2,sub_self,Real.cos_zero]
      exact actual_profile_margin_le_one
  · by_cases hj : j ∈ Set.range e.nodes
    · obtain ⟨y,hy⟩ := hj
      have hz := actual_inside_outside_edge_profiles_zero G hR e y i hi (by rw [hy]; exact G.adj_symm hadj)
      rw [←hy,hz.1,hz.2,sub_self,Real.cos_zero]
      exact actual_profile_margin_le_one
    · rw [actual_embedded_profile_outside e.nodes i hi,actual_embedded_profile_outside e.nodes j hj,sub_self,Real.cos_zero]
      exact actual_profile_margin_le_one
end Reference.MD06CleanCycle
