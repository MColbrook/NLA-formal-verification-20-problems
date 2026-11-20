module

public import NLA.MD06.CleanCycleGraph.EmbeddedProfile

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction
attribute [local instance] Classical.propDecidable

theorem actual_gradient_real_neighbor_sum {n : ℕ} (G : SimpleGraph (Fin n))
    (phi : Fin n → ℝ) (v : Fin n) :
    Gradient G (PhaseLift phi) v = ∑ w ∈ G.neighborFinset v, Real.sin (phi v-phi w) := by
  rw [G.neighborFinset_eq_filter,Finset.sum_filter]
  unfold Gradient
  apply Finset.sum_congr rfl
  intro w hw
  split_ifs
  · change Real.Angle.sin ((phi v : Real.Angle)-(phi w : Real.Angle)) = Real.sin (phi v-phi w)
    rw [←Real.Angle.coe_sub,Real.Angle.sin_coe]
  · rfl

theorem actual_embedded_gradient_node_sum {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hR : 4 ≤ R) (e : CleanCycleEmbedding (ell := ell) G hR) (x : TreeNodes ell R) :
    Gradient G (PhaseLift (fun v => EmbeddedProfile e.nodes v)) (e.nodes x) =
      ∑ y ∈ TreeNeighbors hR x, Real.sin (NodeProfile x-NodeProfile y) := by
  rw [actual_gradient_real_neighbor_sum]
  have hs : (TreeNeighbors hR x).image e.nodes ⊆ G.neighborFinset (e.nodes x) := by
    intro v hv
    rw [←e.induced_neighbors x] at hv
    exact (Finset.mem_inter.mp hv).1
  have he : (∑ v ∈ (TreeNeighbors hR x).image e.nodes,
      Real.sin (EmbeddedProfile e.nodes (e.nodes x)-EmbeddedProfile e.nodes v)) =
      ∑ v ∈ G.neighborFinset (e.nodes x), Real.sin (EmbeddedProfile e.nodes (e.nodes x)-EmbeddedProfile e.nodes v) := by
    apply Finset.sum_subset hs
    intro v hv hout
    by_cases hin : v ∈ Finset.univ.image e.nodes
    · have hmem : v ∈ G.neighborFinset (e.nodes x) ∩ Finset.univ.image e.nodes := Finset.mem_inter.mpr ⟨hv,hin⟩
      rw [e.induced_neighbors x] at hmem
      exact False.elim (hout hmem)
    · have hvout : v ∉ Set.range e.nodes := by
        intro hh
        obtain ⟨y,hy⟩ := hh
        exact hin (Finset.mem_image.mpr ⟨y,Finset.mem_univ y,hy⟩)
      have hx : x.1.val = R := by
        have hle := x.1.isLt
        by_contra hh
        have hlt : x.1.val < R := by omega
        exact hin (e.closed_interior x hlt hv)
      rw [actual_embedded_leaf_profile_zero e.nodes x hx,actual_embedded_profile_outside e.nodes v hvout]
      simp
  rw [←he,Finset.sum_image (by intro a ha b hb hab; exact e.nodes.injective hab)]
  simp only [actual_embedded_profile_at_node]

theorem actual_embedded_gradient_outside_zero {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hR : 4 ≤ R) (e : CleanCycleEmbedding (ell := ell) G hR) (v : Fin n) (hv : v ∉ Set.range e.nodes) :
    Gradient G (PhaseLift (fun a => EmbeddedProfile e.nodes a)) v = 0 := by
  rw [actual_gradient_real_neighbor_sum]
  apply Finset.sum_eq_zero
  intro w hw
  rw [actual_embedded_profile_outside e.nodes v hv]
  by_cases hin : w ∈ Set.range e.nodes
  · obtain ⟨x,hx⟩ := hin
    have hleaf : x.1.val = R := by
      have hle := x.1.isLt
      by_contra hh
      have hlt : x.1.val < R := by omega
      have hadj : G.Adj (e.nodes x) v := by
        rw [hx]
        exact G.adj_symm ((G.mem_neighborFinset v w).mp hw)
      have himage := e.closed_interior x hlt ((G.mem_neighborFinset (e.nodes x) v).mpr hadj)
      obtain ⟨y,hy,hey⟩ := Finset.mem_image.mp himage
      exact hv ⟨y,hey⟩
    rw [←hx,actual_embedded_leaf_profile_zero e.nodes x hleaf]
    simp
  · rw [actual_embedded_profile_outside e.nodes w hin]
    simp
end Reference.MD06CleanCycle
