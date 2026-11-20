module

public import NLA.MD06.RadiusEmbedding.PaperLayers

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] [DecidableEq V] in
theorem actual_radius_forest_vertex_original_radius {v : V} (c : G.Walk v v) (R : ℕ)
    (r x : CycleRadius G c R) (hr : r ∈ (LiftedCycle c R).support)
    (hreach : (RadiusForest G c R).Reachable r x) :
    x.val ∈ CycleRadius G c ((RadiusForest G c R).dist r x) := by
  obtain ⟨p, hp, hplen⟩ := hreach.exists_path_of_dist
  let b := (p.mapLe ((G.induce (CycleRadius G c R)).deleteEdges_le _)).map
    (Embedding.induce _).toHom
  have hbound : G.dist r.val x.val ≤ (RadiusForest G c R).dist r x := by
    have := SimpleGraph.dist_le b
    change G.dist r.val x.val ≤ b.length at this
    simpa only [b, Walk.length_map, Walk.length_mapLe, hplen] using this
  refine ⟨r.val, actual_lifted_cycle_vertex_mem c R hr, b.reachable.symm, ?_⟩
  rwa [dist_comm]

omit [Fintype V] [DecidableEq V] in
theorem actual_radius_forest_closed_interior {v : V} (c : G.Walk v v) (R : ℕ)
    (r x : CycleRadius G c R) (hr : r ∈ (LiftedCycle c R).support)
    (hreach : (RadiusForest G c R).Reachable r x)
    (hinterior : (RadiusForest G c R).dist r x < R) :
    G.neighborSet x.val ⊆ CycleRadius G c R := by
  intro y hy
  apply actual_cycle_radius_mono c (show (RadiusForest G c R).dist r x + 1 ≤ R by omega)
  exact actual_cycle_radius_neighbors_closed c _
    (actual_radius_forest_vertex_original_radius c R r x hr hreach) hy

end Reference.MD06RadiusEmbedding
