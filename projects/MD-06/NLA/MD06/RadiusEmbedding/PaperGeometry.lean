module

public import NLA.MD06.RadiusEmbedding.RadiusInduced

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} {G : SimpleGraph V}

def CleanRadius {v : V} (G : SimpleGraph V) (c : G.Walk v v) (R : ℕ) : Prop :=
  UniqueCycleEdges (LiftedCycle c R)

theorem actual_cycle_radius_mono {v : V} (c : G.Walk v v) {r R : ℕ} (hr : r ≤ R) :
    CycleRadius G c r ⊆ CycleRadius G c R := by
  rintro x ⟨u, hu, hxu, hd⟩
  exact ⟨u, hu, hxu, hd.trans hr⟩

theorem actual_lifted_cycle_vertex_mem {v : V} (c : G.Walk v v) (R : ℕ)
    {x : CycleRadius G c R} (hx : x ∈ (LiftedCycle c R).support) : x.val ∈ c.support := by
  have hm : x.val ∈ ((LiftedCycle c R).map (Embedding.induce _).toHom).support := by
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  simpa only [LiftedCycle, Walk.map_induce] using hm

variable [Fintype V] [DecidableEq V]

theorem actual_clean_radius_root_forest_degree_one {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R)
    (hcubic : ∀ x : V, G.degree x = 3)
    (r : CycleRadius G c R) (hr : r ∈ (LiftedCycle c R).support) :
    ((G.induce (CycleRadius G c R)).deleteEdges {e | e ∈ (LiftedCycle c R).edges}).degree r = 1 := by
  have hrG := actual_lifted_cycle_vertex_mem c R hr
  have hd : (G.induce (CycleRadius G c R)).degree r = 3 := by
    calc
      (G.induce (CycleRadius G c R)).degree r = G.degree r.val := by
        apply degree_induce_of_neighborSet_subset
        intro y hy
        apply actual_cycle_radius_mono c hR
        exact actual_cycle_radius_neighbors_closed c 0
          (actual_cycle_member_radius c 0 hrG) hy
      _ = 3 := hcubic r.val
  convert! actual_cycle_root_forest_degree_one (LiftedCycle c R) hc.1 hr hd using 1

theorem actual_clean_radius_interior_forest_degree_three {v : V} (c : G.Walk v v)
    (R : ℕ) (hc : CleanRadius G c R)
    (hcubic : ∀ x : V, G.degree x = 3)
    (r x : CycleRadius G c R) (hr : r ∈ (LiftedCycle c R).support)
    (hreach : ((G.induce (CycleRadius G c R)).deleteEdges
      {e | e ∈ (LiftedCycle c R).edges}).Reachable r x)
    (hpos : 0 < ((G.induce (CycleRadius G c R)).deleteEdges
      {e | e ∈ (LiftedCycle c R).edges}).dist r x)
    (hinterior : ((G.induce (CycleRadius G c R)).deleteEdges
      {e | e ∈ (LiftedCycle c R).edges}).dist r x < R) :
    ((G.induce (CycleRadius G c R)).deleteEdges
      {e | e ∈ (LiftedCycle c R).edges}).degree x = 3 := by
  let H := G.induce (CycleRadius G c R)
  let F := H.deleteEdges {e | e ∈ (LiftedCycle c R).edges}
  change 0 < F.dist r x at hpos
  change F.dist r x < R at hinterior
  have hxnot : x ∉ (LiftedCycle c R).support := by
    intro hx
    have he : r = x := actual_unique_cycle_forest_roots_separated
      (LiftedCycle c R) hc (actual_cycle_radius_induced_connected c R) hr hx hreach
    subst x
    simp only [dist_self] at hpos
    omega
  obtain ⟨p, hp, hplen⟩ := hreach.exists_path_of_dist
  let bH : H.Walk r x := p.mapLe (H.deleteEdges_le _)
  let bG : G.Walk r.val x.val := bH.map (Embedding.induce _).toHom
  have hbound : G.dist r.val x.val ≤ F.dist r x := by
    have := SimpleGraph.dist_le bG
    simpa only [bG, bH, Walk.length_map, Walk.length_mapLe, hplen] using this
  have hrG := actual_lifted_cycle_vertex_mem c R hr
  have hxd : x.val ∈ CycleRadius G c (F.dist r x) := by
    refine ⟨r.val, hrG, bG.reachable.symm, ?_⟩
    rwa [dist_comm]
  have hd : H.degree x = 3 := by
    calc
      H.degree x = G.degree x.val := by
        apply degree_induce_of_neighborSet_subset
        intro y hy
        apply actual_cycle_radius_mono c (show F.dist r x + 1 ≤ R by omega)
        exact actual_cycle_radius_neighbors_closed c _ hxd hy
      _ = 3 := hcubic x.val
  convert! actual_noncycle_forest_degree_three (LiftedCycle c R) hxnot hd using 1

end Reference.MD06RadiusEmbedding
