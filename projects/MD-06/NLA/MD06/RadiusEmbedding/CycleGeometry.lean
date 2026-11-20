module

public import NLA.MD06.RadiusEmbedding.TreeCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Reference.MD06RadiusEmbedding
open SimpleGraph
open Reference.MD06CleanCycle
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

omit [Fintype V] in
theorem actual_radius_cycle_coordinate_getVert {v : V} (c : G.Walk v v)
    (R : ℕ) (hc : CleanRadius G c R) (i : Fin c.length) :
    (RadiusCycleCoordinate c R hc i).val.val = c.getVert i.val := by
  change ((LiftedCycle c R).getVert i.val).val = c.getVert i.val
  have he : (LiftedCycle c R).map (Embedding.induce _).toHom = c := c.map_induce _
  have hg := congrArg (fun p => p.getVert i.val) he
  simpa only [Walk.getVert_map,Embedding.coe_toHom,Embedding.induce,Embedding.comap_apply,Function.Embedding.subtype_apply] using hg

theorem actual_radius_nodes_root_eq_getVert {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (i : Fin c.length) :
    ActualRadiusNodes c R hR hc hcubic (RootNode i) = c.getVert i.val :=
  actual_radius_cycle_coordinate_getVert c R hc i

theorem actual_radius_tree_coordinate_root {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (i : Fin c.length) :
    RadiusTreeCoordinate c R hR hc hcubic (RootNode i) =
      (RadiusCycleCoordinate c R hc i).val := rfl

theorem actual_next_previous_root {ell : ℕ} (i : Fin ell) :
    NextRoot (PreviousRoot i) = i := by
  apply Fin.ext
  have hi := i.isLt
  by_cases h0 : i.val = 0
  · have hprev : (i.val+ell-1)%ell = ell-1 := by
      rw [h0]
      simpa only [Nat.zero_add] using Nat.mod_eq_of_lt (show ell-1 < ell by omega)
    simp only [NextRoot,PreviousRoot,hprev]
    have he : ell-1+1=ell := by omega
    rw [he,Nat.mod_self,h0]
  · have hprev : (i.val+ell-1)%ell = i.val-1 := by
      have he : i.val+ell-1 = (i.val-1)+ell := by omega
      rw [he,Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    simp only [NextRoot,PreviousRoot,hprev]
    have he : i.val-1+1=i.val := by omega
    rw [he,Nat.mod_eq_of_lt hi]

theorem actual_radius_nodes_nextroot_adj {v : V} (c : G.Walk v v) (hc0 : c.IsCycle)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (i : Fin c.length) :
    G.Adj (ActualRadiusNodes c R hR hc hcubic (RootNode i))
      (ActualRadiusNodes c R hR hc hcubic (RootNode (NextRoot i))) := by
  rw [actual_radius_nodes_root_eq_getVert,actual_radius_nodes_root_eq_getVert]
  have h := actual_cycle_coordinate_next_adj c hc0 i
  exact c.toSubgraph.adj_sub h

theorem actual_radius_nodes_previousroot_adj {v : V} (c : G.Walk v v) (hc0 : c.IsCycle)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (i : Fin c.length) :
    G.Adj (ActualRadiusNodes c R hR hc hcubic (RootNode i))
      (ActualRadiusNodes c R hR hc hcubic (RootNode (PreviousRoot i))) := by
  have h := actual_radius_nodes_nextroot_adj c hc0 R hR hc hcubic (PreviousRoot i)
  rw [actual_next_previous_root] at h
  exact h.symm

end Reference.MD06RadiusEmbedding
