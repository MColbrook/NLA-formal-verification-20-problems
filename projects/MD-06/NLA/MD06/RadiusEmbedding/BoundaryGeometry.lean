module

public import NLA.MD06.RadiusEmbedding.BranchAdjacency
public import NLA.MD06.RadiusEmbedding.CycleGeometry

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Reference.MD06RadiusEmbedding
open SimpleGraph
open Reference.MD06CleanCycle
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem actual_radius_tree_positive_notcycle {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x : TreeNodes c.length R) (h0 : 0 < x.1.val) :
    RadiusTreeCoordinate c R hR hc hcubic x ∉ (LiftedCycle c R).support := by
  intro hx
  have hcoord := actual_radius_tree_coordinate_reachable_distance c R hR hc hcubic x
  have he := actual_unique_cycle_forest_roots_separated (LiftedCycle c R) hc
    (actual_cycle_radius_induced_connected c R)
    (List.mem_toFinset.mp (RadiusCycleCoordinate c R hc x.2.1).property) hx hcoord.1
  rw [he,dist_self] at hcoord
  omega

theorem actual_radius_tree_boundary_neighbor_parent {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x y : TreeNodes c.length R) (hxR : x.1.val = R)
    (hxy : G.Adj (ActualRadiusNodes c R hR hc hcubic x)
      (ActualRadiusNodes c R hR hc hcubic y)) :
    y = ParentNode x (by omega) := by
  have h0 : 0 < x.1.val := by omega
  have hxnot := actual_radius_tree_positive_notcycle c R hR hc hcubic x h0
  have hH : (G.induce (CycleRadius G c R)).Adj
      (RadiusTreeCoordinate c R hR hc hcubic x) (RadiusTreeCoordinate c R hR hc hcubic y) := hxy
  have hF : (RadiusForest G c R).Adj
      (RadiusTreeCoordinate c R hR hc hcubic x) (RadiusTreeCoordinate c R hR hc hcubic y) := by
    apply deleteEdges_adj.mpr
    refine ⟨hH,?_⟩
    intro he
    exact hxnot ((LiftedCycle c R).fst_mem_support_of_mem_edges he)
  have hx := actual_radius_tree_coordinate_reachable_distance c R hR hc hcubic x
  have hy := actual_radius_tree_coordinate_reachable_distance c R hR hc hcubic y
  have hr : (RadiusCycleCoordinate c R hc x.2.1).val =
      (RadiusCycleCoordinate c R hc y.2.1).val :=
    actual_unique_cycle_forest_roots_separated (LiftedCycle c R) hc
      (actual_cycle_radius_induced_connected c R)
      (List.mem_toFinset.mp (RadiusCycleCoordinate c R hc x.2.1).property)
      (List.mem_toFinset.mp (RadiusCycleCoordinate c R hc y.2.1).property)
      ((hx.1.trans hF.reachable).trans hy.1.symm)
  have hydepth := hy.2
  rw [← hr] at hydepth
  have hstep := (RadiusAcyclic c R hc).dist_eq_dist_add_one_of_adj_of_reachable
    (RadiusCycleCoordinate c R hc x.2.1).val hF hx.1
  have hylt := y.1.isLt
  have hlow : (RadiusForest G c R).dist (RadiusCycleCoordinate c R hc x.2.1).val
      (RadiusTreeCoordinate c R hR hc hcubic y) + 1 =
      (RadiusForest G c R).dist (RadiusCycleCoordinate c R hc x.2.1).val
      (RadiusTreeCoordinate c R hR hc hcubic x) := by
    rcases hstep with h | h
    · exact h.symm
    · omega
  have hp := actual_radius_tree_parent_adj c R hR hc hcubic x h0
  have hpdepth := (actual_radius_tree_coordinate_reachable_distance c R hR hc hcubic
    (ParentNode x h0)).2
  change (RadiusForest G c R).dist (RadiusCycleCoordinate c R hc x.2.1).val
    (RadiusTreeCoordinate c R hR hc hcubic (ParentNode x h0)) = x.1.val-1 at hpdepth
  have he := actual_forest_parent_unique (RadiusAcyclic c R hc) hx.1 hF hp.symm hlow
    (by omega)
  exact (actual_radius_tree_coordinate_bijective c R hR hc hcubic).1 he

end Reference.MD06RadiusEmbedding
