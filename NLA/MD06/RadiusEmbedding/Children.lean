module

public import NLA.MD06.RadiusEmbedding.Degrees

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def ForwardChildren (G : SimpleGraph V) (root v : V) : Finset V :=
  (G.neighborFinset v).filter (fun w => G.dist root w = G.dist root v + 1)

theorem actual_forest_forward_children_erase_parent (hG : G.IsAcyclic)
    {root v p : V} (hv : G.Reachable root v) (hp : G.Adj v p)
    (hdp : G.dist root p + 1 = G.dist root v) :
    ForwardChildren G root v = (G.neighborFinset v).erase p := by
  ext w
  simp only [ForwardChildren, Finset.mem_filter, Finset.mem_erase, mem_neighborFinset]
  constructor
  · rintro ⟨hw, hdw⟩
    refine ⟨?_, hw⟩
    intro he
    subst w
    omega
  · rintro ⟨hne, hw⟩
    refine ⟨hw, ?_⟩
    rcases hG.dist_eq_dist_add_one_of_adj_of_reachable root hw hv with hlow | hhigh
    · exact (hne (actual_forest_parent_unique hG hv hw hp hlow.symm hdp)).elim
    · exact hhigh

theorem actual_forest_forward_children_card_two (hG : G.IsAcyclic)
    {root v : V} (hv : G.Reachable root v) (hne : root ≠ v)
    (hd : G.degree v = 3) : (ForwardChildren G root v).card = 2 := by
  obtain ⟨p, hp, _⟩ := actual_forest_parent_exists hG hv hne
  rw [actual_forest_forward_children_erase_parent hG hv hp.1 hp.2,
    Finset.card_erase_of_mem ((G.mem_neighborFinset v p).mpr hp.1),
    card_neighborFinset_eq_degree, hd]

omit [DecidableEq V] in
theorem actual_forest_distinct_parents_disjoint_children (hG : G.IsAcyclic)
    {root v w : V} (hv : G.Reachable root v) (_hw : G.Reachable root w)
    (hne : v ≠ w) : Disjoint (ForwardChildren G root v) (ForwardChildren G root w) := by
  apply Finset.disjoint_left.mpr
  intro z hzv hzw
  simp only [ForwardChildren, Finset.mem_filter, mem_neighborFinset] at hzv hzw
  apply hne
  exact actual_forest_parent_unique hG (hv.trans hzv.1.reachable)
    hzv.1.symm hzw.1.symm hzv.2.symm hzw.2.symm

omit [DecidableEq V] in
theorem actual_root_forward_children_eq_neighbors (root : V) :
    ForwardChildren G root root = G.neighborFinset root := by
  ext w
  simp only [ForwardChildren, Finset.mem_filter, mem_neighborFinset, dist_self, zero_add]
  exact ⟨fun h => h.1, fun h => ⟨h, dist_eq_one_iff_adj.mpr h⟩⟩

theorem actual_cycle_root_forward_children_card_one {v x : V} (c : G.Walk v v)
    (hc : c.IsCycle) (hx : x ∈ c.support) (hd : G.degree x = 3) :
    (ForwardChildren (G.deleteEdges {e | e ∈ c.edges}) x x).card = 1 := by
  rw [actual_root_forward_children_eq_neighbors, card_neighborFinset_eq_degree]
  convert! actual_cycle_root_forest_degree_one c hc hx hd using 1
  unfold SimpleGraph.degree
  congr 1
  ext y
  simp only [mem_neighborFinset]

end Reference.MD06RadiusEmbedding
