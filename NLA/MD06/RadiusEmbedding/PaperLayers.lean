module

public import NLA.MD06.RadiusEmbedding.PaperGeometry

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable abbrev RadiusForest {v : V} (G : SimpleGraph V) (c : G.Walk v v) (R : ℕ) :=
  (G.induce (CycleRadius G c R)).deleteEdges {e | e ∈ (LiftedCycle c R).edges}

noncomputable def RadiusRootLayer {v : V} (G : SimpleGraph V) (c : G.Walk v v)
    (R j : ℕ) : Finset (CycleRadius G c R) :=
  (LiftedCycle c R).support.toFinset.biUnion (fun r => DistanceLayer (RadiusForest G c R) r j)

omit [Fintype V] in
theorem actual_cycle_support_card_length {v : V} (c : G.Walk v v) (hc : c.IsCycle) :
    c.support.toFinset.card = c.length := by
  cases c with
  | nil => exact (hc.not_nil Walk.Nil.nil).elim
  | cons h p =>
    have hp : p.IsPath := (Walk.cons_isCycle_iff p h).mp hc |>.1
    rw [Walk.support_cons, List.toFinset_cons,
      Finset.insert_eq_of_mem (List.mem_toFinset.mpr p.end_mem_support),
      List.toFinset_card_of_nodup hp.support_nodup, Walk.length_support,
      Walk.length_cons]

set_option maxHeartbeats 2000000 in
theorem actual_clean_radius_single_root_layer_card {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R)
    (hcubic : ∀ x : V, G.degree x = 3)
    (r : CycleRadius G c R) (hr : r ∈ (LiftedCycle c R).support)
    (j : ℕ) (hj : 1 ≤ j) (hjR : j ≤ R) :
    (DistanceLayer (RadiusForest G c R) r j).card = 2 ^ (j - 1) := by
  have hacyc : (RadiusForest G c R).IsAcyclic :=
    actual_unique_cycle_deletion_forest (G := G.induce (CycleRadius G c R))
      (LiftedCycle c R) hc
  have hroot : (RadiusForest G c R).degree r = 1 :=
    actual_clean_radius_root_forest_degree_one (G := G) c R hR hc hcubic r hr
  have hinterior : ∀ x : CycleRadius G c R,
      (RadiusForest G c R).Reachable r x →
      0 < (RadiusForest G c R).dist r x →
      (RadiusForest G c R).dist r x < R → (RadiusForest G c R).degree x = 3 := by
    intro x hx hp hlt
    exact actual_clean_radius_interior_forest_degree_three (G := G)
      c R hc hcubic r x hr hx hp hlt
  apply actual_forest_binary_layer_card (G := RadiusForest G c R)
    hacyc r R ?_ ?_ j hj hjR
  · convert! hroot using 1
    unfold SimpleGraph.degree
    congr 1
    ext y
    simp only [mem_neighborFinset]
  · intro x hx hp hlt
    convert! hinterior x hx hp hlt using 1
    unfold SimpleGraph.degree
    congr 1
    ext y
    simp only [mem_neighborFinset]

theorem actual_clean_radius_root_layers_pairwise_disjoint {v : V} (c : G.Walk v v)
    (R j : ℕ) (hc : CleanRadius G c R) :
    (↑(LiftedCycle c R).support.toFinset : Set (CycleRadius G c R)).PairwiseDisjoint
      (fun r => DistanceLayer (RadiusForest G c R) r j) := by
  intro r hr s hs hne
  apply Finset.disjoint_left.mpr
  intro x hxr hxs
  have hrx : (RadiusForest G c R).Reachable r x := (Finset.mem_filter.mp hxr).2.1
  have hsx : (RadiusForest G c R).Reachable s x := (Finset.mem_filter.mp hxs).2.1
  apply hne
  exact actual_unique_cycle_forest_roots_separated (LiftedCycle c R) hc
    (actual_cycle_radius_induced_connected c R) (List.mem_toFinset.mp hr)
    (List.mem_toFinset.mp hs) (hrx.trans hsx.symm)

theorem actual_clean_radius_total_layer_card {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R)
    (hcubic : ∀ x : V, G.degree x = 3)
    (j : ℕ) (hj : 1 ≤ j) (hjR : j ≤ R) :
    (RadiusRootLayer G c R j).card = c.length * 2 ^ (j - 1) := by
  unfold RadiusRootLayer
  rw [Finset.card_biUnion (actual_clean_radius_root_layers_pairwise_disjoint c R j hc)]
  calc
    ∑ r ∈ (LiftedCycle c R).support.toFinset,
        (DistanceLayer (RadiusForest G c R) r j).card =
      ∑ _r ∈ (LiftedCycle c R).support.toFinset, 2 ^ (j - 1) := by
        apply Finset.sum_congr rfl
        intro r hr
        exact actual_clean_radius_single_root_layer_card c R hR hc hcubic r
          (List.mem_toFinset.mp hr) j hj hjR
    _ = (LiftedCycle c R).support.toFinset.card * 2 ^ (j - 1) := by simp
    _ = c.length * 2 ^ (j - 1) := by
      rw [actual_cycle_support_card_length _ hc.1, actual_lifted_cycle_length]

end Reference.MD06RadiusEmbedding
