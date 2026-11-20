module

public import NLA.MD06.RadiusEmbedding.PaperGeometry
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Reference.MD06CleanRadiusCardinality
open SimpleGraph
open Reference.MD06RadiusEmbedding
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem actual_delete_one_edge_card {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    (G.deleteEdges {e}).edgeFinset.card + 1 = G.edgeFinset.card := by
  have h := Finset.card_erase_add_one he
  have hd : (G.deleteEdges {e}).edgeFinset = G.edgeFinset.erase e := by
    ext f
    simp [edgeSet_deleteEdges, and_comm]
  rw [hd]
  exact h

theorem actual_connected_cycle_card {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (hconn : G.Connected) :
    Fintype.card V ≤ G.edgeFinset.card := by
  obtain ⟨e, he⟩ := c.edges.exists_mem_of_ne_nil (by simp [hc.not_nil])
  obtain ⟨x, y⟩ := e
  have hn : ¬ G.IsBridge s(x, y) :=
    fun hb => hb.notMem_edges_of_isCycle hc he
  have hd := hconn.preconnected.connected_deleteEdges_of_not_isBridge hn
  have hcard := hd.card_vert_le_card_edgeSet_add_one
  have he' : s(x, y) ∈ G.edgeFinset := by
    simpa only [mem_edgeFinset] using c.edges_subset_edgeSet he
  have hdel := actual_delete_one_edge_card he'
  simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card, hdel] using hcard

theorem actual_small_connected_cycle_universal_edge {v u : V}
    (c : G.Walk v v) (p : G.Walk u u)
    (hc : c.IsCycle) (hp : p.IsCycle) (hconn : G.Connected)
    (hsmall : G.edgeFinset.card ≤ Fintype.card V)
    {e : Sym2 V} (he : e ∈ p.edges) : e ∈ c.edges := by
  obtain ⟨x, y⟩ := e
  have hn : ¬ G.IsBridge s(x, y) :=
    fun hb => hb.notMem_edges_of_isCycle hp he
  have hd := hconn.preconnected.connected_deleteEdges_of_not_isBridge hn
  have he' : s(x, y) ∈ G.edgeFinset := by
    simpa only [mem_edgeFinset] using p.edges_subset_edgeSet he
  have hdel := actual_delete_one_edge_card he'
  have hlarge := actual_connected_cycle_card p hp hconn
  have ht : (G.deleteEdges {s(x, y)}).IsTree := by
    apply isTree_iff_connected_and_card.mpr
    refine ⟨hd, ?_⟩
    have heq := Nat.le_antisymm hsmall hlarge
    simpa only [Nat.card_eq_fintype_card, ← edgeFinset_card] using hdel.trans heq
  by_contra hnot
  have hav : ∀ f, f ∈ c.edges → f ∉ ({s(x, y)} : Set (Sym2 V)) := by
    intro f hf hfe
    have : f = s(x, y) := Set.mem_singleton_iff.mp hfe
    exact hnot (by simpa only [this] using hf)
  exact ht.2 (c.toDeleteEdges {s(x, y)} hav) (Walk.IsCycle.toDeleteEdges G ({s(x, y)} : Set (Sym2 V)) hc hav)

theorem actual_small_connected_cycle_unique {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (hconn : G.Connected)
    (hsmall : G.edgeFinset.card ≤ Fintype.card V) : UniqueCycleEdges c := by
  refine ⟨hc, ?_⟩
  intro u p hp e
  exact ⟨fun he => actual_small_connected_cycle_universal_edge c p hc hp hconn hsmall he,
    fun he => actual_small_connected_cycle_universal_edge p c hp hc hconn hsmall he⟩

theorem actual_unclean_radius_excess_edges {v : V} (c : G.Walk v v)
    (hc : c.IsCycle) (R : ℕ) (hunclean : ¬ CleanRadius G c R) :
    Fintype.card (CycleRadius G c R) + 1 ≤
      (G.induce (CycleRadius G c R)).edgeFinset.card := by
  by_contra hcard
  apply hunclean
  exact actual_small_connected_cycle_unique (LiftedCycle c R)
    (actual_lifted_cycle_isCycle c R hc) (actual_cycle_radius_induced_connected c R)
    (by omega)

#print axioms actual_delete_one_edge_card
#print axioms actual_connected_cycle_card
#print axioms actual_small_connected_cycle_universal_edge
#print axioms actual_small_connected_cycle_unique
#print axioms actual_unclean_radius_excess_edges

end Reference.MD06CleanRadiusCardinality
