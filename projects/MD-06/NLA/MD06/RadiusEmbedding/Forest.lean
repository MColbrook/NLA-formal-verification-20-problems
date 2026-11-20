module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def UniqueCycleEdges {v : V} (c : G.Walk v v) : Prop :=
  c.IsCycle ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle →
    ∀ e : Sym2 V, e ∈ p.edges ↔ e ∈ c.edges

theorem actual_delete_cycle_transversal_acyclic (S : Set (Sym2 V))
    (hS : ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → ∃ e ∈ p.edges, e ∈ S) :
    (G.deleteEdges S).IsAcyclic := by
  classical
  intro u p hp
  have hle := G.deleteEdges_le S
  obtain ⟨e, he, heS⟩ := hS (p.mapLe hle) (hp.mapLe hle)
  have hep : e ∈ p.edges := by
    simpa only [Walk.edges_map, Hom.coe_ofLE, Sym2.map_id,
      List.map_id_fun, id_eq] using he
  have hn : e ∉ S := by
    have := p.edges_subset_edgeSet hep
    rw [edgeSet_deleteEdges] at this
    exact this.2
  exact hn heS

theorem actual_unique_cycle_deletion_forest {v : V} (c : G.Walk v v)
    (hc : UniqueCycleEdges c) :
    (G.deleteEdges {e | e ∈ c.edges}).IsAcyclic := by
  apply actual_delete_cycle_transversal_acyclic
  intro u p hp
  have hne : p.edges ≠ [] := by
    intro he
    have : p.length = 0 := by
      simpa only [Walk.length_edges, List.length_nil] using congrArg List.length he
    have hlen := hp.three_le_length
    omega
  obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil p.edges hne
  exact ⟨e, he, (hc.2 p hp e).mp he⟩

theorem actual_unique_cycle_deleted_component_tree {v : V} (c : G.Walk v v)
    (hc : UniqueCycleEdges c)
    (K : (G.deleteEdges {e | e ∈ c.edges}).ConnectedComponent) :
    K.toSimpleGraph.IsTree := by
  exact (actual_unique_cycle_deletion_forest c hc).isTree_connectedComponent K

theorem actual_unique_cycle_noncycle_edge_bridge {v : V} (c : G.Walk v v)
    (hc : UniqueCycleEdges c) {e : Sym2 V} (he : e ∈ G.edgeSet)
    (hne : e ∉ c.edges) : G.IsBridge e := by
  apply (isBridge_iff_forall_cycle_notMem he).mpr
  intro u p hp hep
  exact hne ((hc.2 p hp e).mp hep)

theorem actual_unique_cycle_delete_one_edge_tree {v x y : V} (c : G.Walk v v)
    (hc : UniqueCycleEdges c) (hconn : G.Connected)
    (he : s(x, y) ∈ c.edges) : (G.deleteEdges {s(x, y)}).IsTree := by
  refine ⟨?_, ?_⟩
  · apply hconn.preconnected.connected_deleteEdges_of_not_isBridge
    intro hb
    exact hb.notMem_edges_of_isCycle hc.1 he
  · apply actual_delete_cycle_transversal_acyclic
    intro u p hp
    exact ⟨s(x, y), (hc.2 p hp _).mpr he, Set.mem_singleton _⟩

end Reference.MD06RadiusEmbedding
