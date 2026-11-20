module

public import NLA.MD06.RadiusEmbedding.NodeFrames

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} {G : SimpleGraph V}

theorem actual_lifted_cycle_vertex_mem_iff {v : V} (c : G.Walk v v) (R : ℕ)
    (x : CycleRadius G c R) :
    x ∈ (LiftedCycle c R).support ↔ x.val ∈ c.support := by
  constructor
  · exact actual_lifted_cycle_vertex_mem c R
  · intro hx
    have hm : x.val ∈ ((LiftedCycle c R).map (Embedding.induce _).toHom).support := by
      simpa only [LiftedCycle, Walk.map_induce] using hx
    rw [Walk.support_map] at hm
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hm
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy

theorem actual_radius_forest_bounded_root {v : V} (c : G.Walk v v) (R : ℕ)
    (x : CycleRadius G c R) :
    ∃ r : CycleRadius G c R, r ∈ (LiftedCycle c R).support ∧
      (RadiusForest G c R).Reachable r x ∧
      (RadiusForest G c R).dist r x ≤ R := by
  obtain ⟨u,hu,hxu,hd⟩ := x.property
  obtain ⟨p,hp,hlen⟩ := hxu.exists_path_of_dist
  have hps := actual_short_walk_cycle_radius_support c R hu p (hlen.trans_le hd)
  let b := p.induce (CycleRadius G c R) hps
  have hu' : (⟨u,hps u p.end_mem_support⟩ : CycleRadius G c R) ∈
      (LiftedCycle c R).support :=
    (actual_lifted_cycle_vertex_mem_iff c R _).mpr hu
  obtain ⟨r,hr,q,hq⟩ := actual_walk_hits_cycle_bounded (LiftedCycle c R) b hu'
  have hreach : (RadiusForest G c R).Reachable x r := q.reachable
  refine ⟨r,hr,hreach.symm,?_⟩
  rw [dist_comm]
  have hdq := SimpleGraph.dist_le q
  have he : b.map (Embedding.induce _).toHom = p := p.map_induce _
  have hblen : b.length = p.length := (Walk.length_map _ _).symm.trans (congrArg Walk.length he)
  exact hdq.trans (hq.trans (hblen.trans_le (hlen.trans_le hd)))

theorem actual_clean_radius_root_unique_bounded {v : V} (c : G.Walk v v)
    (R : ℕ) (hc : CleanRadius G c R) (x : CycleRadius G c R) :
    ∃! r : CycleRadius G c R, r ∈ (LiftedCycle c R).support ∧
      (RadiusForest G c R).Reachable r x ∧ (RadiusForest G c R).dist r x ≤ R := by
  obtain ⟨r,hr,hrx,hd⟩ := actual_radius_forest_bounded_root c R x
  refine ⟨r,⟨hr,hrx,hd⟩,?_⟩
  intro s hs
  exact actual_unique_cycle_forest_roots_separated (LiftedCycle c R) hc
    (actual_cycle_radius_induced_connected c R) hs.1 hr (hs.2.1.trans hrx.symm)

end Reference.MD06RadiusEmbedding
