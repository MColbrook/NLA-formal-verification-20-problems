module

public import NLA.MD06.RadiusEmbedding.Layers

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} {G : SimpleGraph V}

def CycleRadius {v : V} (G : SimpleGraph V) (c : G.Walk v v) (R : ℕ) : Set V :=
  {x | ∃ u ∈ c.support, G.Reachable x u ∧ G.dist x u ≤ R}

theorem actual_walk_hits_cycle_bounded {v x y : V} (c : G.Walk v v)
    (b : G.Walk x y) (hy : y ∈ c.support) :
    ∃ u ∈ c.support, ∃ p : (G.deleteEdges {e | e ∈ c.edges}).Walk x u,
      p.length ≤ b.length := by
  induction b with
  | nil => exact ⟨_, hy, Walk.nil, Nat.le_refl 0⟩
  | @cons x y z h b ih =>
    by_cases he : s(x, y) ∈ c.edges
    · exact ⟨x, c.fst_mem_support_of_mem_edges he, Walk.nil, Nat.zero_le _⟩
    · obtain ⟨u, hu, p, hlen⟩ := ih hy
      refine ⟨u, hu, Walk.cons (deleteEdges_adj.mpr ⟨h, he⟩) p, ?_⟩
      simpa only [Walk.length_cons] using Nat.add_le_add_right hlen 1

theorem actual_unique_cycle_radius_iff_forest_distance {v x r : V} (c : G.Walk v v)
    (hc : UniqueCycleEdges c) (hconn : G.Connected) (hr : r ∈ c.support)
    (hxr : (G.deleteEdges {e | e ∈ c.edges}).Reachable x r) (R : ℕ) :
    x ∈ CycleRadius G c R ↔ (G.deleteEdges {e | e ∈ c.edges}).dist x r ≤ R := by
  constructor
  · rintro ⟨u, hu, hxu, hd⟩
    obtain ⟨b, hb, hlen⟩ := hxu.exists_path_of_dist
    obtain ⟨w, hw, p, hp⟩ := actual_walk_hits_cycle_bounded c b hu
    have he : w = r := actual_unique_cycle_forest_roots_separated c hc hconn hw hr
      (p.reachable.symm.trans hxr)
    subst w
    exact (SimpleGraph.dist_le p).trans (hp.trans (hlen.trans_le hd))
  · intro hd
    obtain ⟨p, hp, hlen⟩ := hxr.exists_path_of_dist
    let b : G.Walk x r := p.mapLe (G.deleteEdges_le _)
    refine ⟨r, hr, b.reachable, ?_⟩
    have hblen : b.length = (G.deleteEdges {e | e ∈ c.edges}).dist x r := by
      simpa only [b, Walk.length_map] using hlen
    exact (SimpleGraph.dist_le b).trans (hblen.trans_le hd)

theorem actual_cycle_radius_neighbors_closed {v x y : V} (c : G.Walk v v)
    (R : ℕ) (hx : x ∈ CycleRadius G c R) (hxy : G.Adj x y) :
    y ∈ CycleRadius G c (R + 1) := by
  obtain ⟨u, hu, hxu, hd⟩ := hx
  refine ⟨u, hu, hxy.symm.reachable.trans hxu, ?_⟩
  have ht := hxy.symm.reachable.dist_triangle_left u
  have he : G.dist y x = 1 := dist_eq_one_iff_adj.mpr hxy.symm
  omega

end Reference.MD06RadiusEmbedding
