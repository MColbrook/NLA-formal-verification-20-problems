module

public import NLA.MD06.RadiusEmbedding.Roots
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def CycleNeighbors {v : V} (c : G.Walk v v) (x : V) : Finset V :=
  Finset.univ.filter (fun y => s(x, y) ∈ c.edges)

theorem actual_cycle_neighbors_subset {v : V} (c : G.Walk v v) (x : V) :
    CycleNeighbors c x ⊆ G.neighborFinset x := by
  intro y hy
  simp only [CycleNeighbors, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  exact (G.mem_neighborFinset x y).mpr (c.adj_of_mem_edges hy)

theorem actual_cycle_neighbors_card_two {v x : V} (c : G.Walk v v)
    (hc : c.IsCycle) (hx : x ∈ c.support) : (CycleNeighbors c x).card = 2 := by
  have heq : (↑(CycleNeighbors c x) : Set V) = c.toSubgraph.neighborSet x := by
    ext y
    simp only [CycleNeighbors, Finset.mem_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, Subgraph.mem_neighborSet,
      Walk.adj_toSubgraph_iff_mem_edges]
  rw [← Set.ncard_coe_finset, heq]
  exact hc.ncard_neighborSet_toSubgraph_eq_two hx

theorem actual_cycle_deleted_neighborFinset {v : V} (c : G.Walk v v) (x : V) :
    (G.deleteEdges {e | e ∈ c.edges}).neighborFinset x =
      G.neighborFinset x \ CycleNeighbors c x := by
  ext y
  simp only [mem_neighborFinset, deleteEdges_adj, Set.mem_ofPred_eq,
    Finset.mem_sdiff, CycleNeighbors, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem actual_cycle_root_forest_degree_one {v x : V} (c : G.Walk v v)
    (hc : c.IsCycle) (hx : x ∈ c.support) (hd : G.degree x = 3) :
    (G.deleteEdges {e | e ∈ c.edges}).degree x = 1 := by
  rw [← card_neighborFinset_eq_degree, actual_cycle_deleted_neighborFinset,
    Finset.card_sdiff_of_subset (actual_cycle_neighbors_subset c x),
    actual_cycle_neighbors_card_two c hc hx, card_neighborFinset_eq_degree, hd]

theorem actual_noncycle_forest_degree_three {v x : V} (c : G.Walk v v)
    (hx : x ∉ c.support) (hd : G.degree x = 3) :
    (G.deleteEdges {e | e ∈ c.edges}).degree x = 3 := by
  have he : CycleNeighbors c x = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hxy : s(x, y) ∈ c.edges := by simpa only [CycleNeighbors,
      Finset.mem_filter, Finset.mem_univ, true_and] using hy
    exact hx (c.fst_mem_support_of_mem_edges hxy)
  rw [← card_neighborFinset_eq_degree, actual_cycle_deleted_neighborFinset,
    he, Finset.sdiff_empty, card_neighborFinset_eq_degree, hd]

end Reference.MD06RadiusEmbedding
