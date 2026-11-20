module

public import NLA.MD06.RadiusEmbedding.Parents

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem actual_unique_cycle_forest_roots_separated {v u w : V} (c : G.Walk v v)
    (hc : UniqueCycleEdges c) (hconn : G.Connected)
    (hu : u ∈ c.support) (hw : w ∈ c.support)
    (huw : (G.deleteEdges {e | e ∈ c.edges}).Reachable u w) : u = w := by
  classical
  cases c with
  | nil => exact (hc.1.not_nil Walk.Nil.nil).elim
  | @cons _ a _ h p =>
    have ht := (Walk.cons_isCycle_iff p h).mp hc.1
    let e : Sym2 V := s(v, a)
    let T := G.deleteEdges {e}
    have hec : e ∈ (Walk.cons h p).edges := by
      simp only [e, Walk.edges_cons, List.mem_cons, true_or]
    have htree : T.IsTree := actual_unique_cycle_delete_one_edge_tree _ hc hconn hec
    let q : T.Walk a v := p.toDeleteEdge e ht.2
    have hqs : q.support = p.support := by
      exact p.support_transfer _
    have hqe : q.edges = p.edges := by
      exact p.edges_transfer _
    have huq : u ∈ q.support := by
      rw [hqs]
      simp only [Walk.support_cons, List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact p.end_mem_support
      · exact hu
    have hwq : w ∈ q.support := by
      rw [hqs]
      simp only [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact p.end_mem_support
      · exact hw
    let d : T.Walk u w := (q.takeUntil u huq).reverse.append (q.takeUntil w hwq)
    have hd : ∀ f ∈ d.bypass.edges, f ∈ (Walk.cons h p).edges := by
      intro f hf
      have hfd := d.edges_bypass_subset_edges hf
      change f ∈ ((q.takeUntil u huq).reverse.append (q.takeUntil w hwq)).edges at hfd
      simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at hfd
      have hfq : f ∈ q.edges := by
        rcases hfd with hfu | hfw
        · exact q.edges_takeUntil_subset_edges huq hfu
        · exact q.edges_takeUntil_subset_edges hwq hfw
      rw [hqe] at hfq
      exact List.mem_cons_of_mem _ hfq
    have hle : G.deleteEdges {f | f ∈ (Walk.cons h p).edges} ≤ T := by
      intro x y hxy
      have htxy := deleteEdges_adj.mp hxy
      apply deleteEdges_adj.mpr
      refine ⟨htxy.1, ?_⟩
      intro hf
      have heq : s(x, y) = e := Set.mem_singleton_iff.mp hf
      exact htxy.2 (heq ▸ hec)
    obtain ⟨b⟩ := huw
    let bT : T.Walk u w := b.bypass.mapLe hle
    have hbT : bT.IsPath := b.bypass_isPath.mapLe hle
    have heq : bT = d.bypass :=
      Subtype.mk.inj (htree.isAcyclic.subsingleton_path u w |>.elim
        ⟨_, hbT⟩ ⟨_, d.bypass_isPath⟩)
    have hempty : b.bypass.edges = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro f hf
      have hfT : f ∈ bT.edges := by
        simpa only [bT, Walk.edges_map, Hom.coe_ofLE, Sym2.map_id,
          List.map_id_fun, id_eq] using hf
      rw [heq] at hfT
      have hfc := hd f hfT
      have hnot := b.bypass.edges_subset_edgeSet hf
      rw [edgeSet_deleteEdges] at hnot
      exact hnot.2 hfc
    exact (Walk.edges_eq_nil.mp hempty).eq

theorem actual_walk_reaches_cycle_root {v x : V} (c : G.Walk v v)
    (b : G.Walk x v) :
    ∃ u ∈ c.support, (G.deleteEdges {e | e ∈ c.edges}).Reachable x u := by
  induction b with
  | nil => exact ⟨_, c.start_mem_support, .refl _⟩
  | @cons x y z h b ih =>
    by_cases he : s(x, y) ∈ c.edges
    · exact ⟨x, c.fst_mem_support_of_mem_edges he, .refl x⟩
    · obtain ⟨u, hu, hreach⟩ := ih c
      exact ⟨u, hu, (deleteEdges_adj.mpr ⟨h, he⟩).reachable.trans hreach⟩

theorem actual_unique_cycle_forest_root_existsUnique {v x : V} (c : G.Walk v v)
    (hc : UniqueCycleEdges c) (hconn : G.Connected) :
    ∃! u : V, u ∈ c.support ∧
      (G.deleteEdges {e | e ∈ c.edges}).Reachable x u := by
  obtain ⟨b⟩ := hconn x v
  obtain ⟨u, hu, hxu⟩ := actual_walk_reaches_cycle_root c b
  refine ⟨u, ⟨hu, hxu⟩, ?_⟩
  intro w hw
  exact actual_unique_cycle_forest_roots_separated c hc hconn hw.1 hu
    (hw.2.symm.trans hxu)

end Reference.MD06RadiusEmbedding
