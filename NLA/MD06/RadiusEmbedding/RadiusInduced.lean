module

public import NLA.MD06.RadiusEmbedding.Distances

@[expose] public section

namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} {G : SimpleGraph V}

theorem actual_cycle_member_radius {v x : V} (c : G.Walk v v)
    (R : ℕ) (hx : x ∈ c.support) : x ∈ CycleRadius G c R := by
  exact ⟨x, hx, .refl x, by simp only [dist_self]; exact Nat.zero_le _⟩

theorem actual_short_walk_cycle_radius_support {v x u : V} (c : G.Walk v v)
    (R : ℕ) (hu : u ∈ c.support) (p : G.Walk x u) (hp : p.length ≤ R) :
    ∀ y ∈ p.support, y ∈ CycleRadius G c R := by
  intro y hy
  let q := p.dropUntil y hy
  refine ⟨u, hu, q.reachable, ?_⟩
  exact (SimpleGraph.dist_le q).trans ((p.length_dropUntil_le_length hy).trans hp)

theorem actual_cycle_radius_induced_connected {v : V} (c : G.Walk v v) (R : ℕ) :
    (G.induce (CycleRadius G c R)).Connected := by
  classical
  let center : CycleRadius G c R :=
    ⟨v, actual_cycle_member_radius c R c.start_mem_support⟩
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨center, ?_⟩
  intro x
  obtain ⟨u, hu, hxu, hd⟩ := x.property
  obtain ⟨p, hp, hplen⟩ := hxu.exists_path_of_dist
  have hps := actual_short_walk_cycle_radius_support c R hu p (hplen.trans_le hd)
  let b := c.takeUntil u hu
  have hbs : ∀ y ∈ b.support, y ∈ CycleRadius G c R := by
    intro y hy
    apply actual_cycle_member_radius c R
    exact c.support_takeUntil_subset_support hu hy
  exact (b.induce _ hbs).reachable.trans (p.induce _ hps).reachable.symm

noncomputable def LiftedCycle {v : V} (c : G.Walk v v) (R : ℕ) :=
  c.induce (CycleRadius G c R) (fun _x hx => actual_cycle_member_radius c R hx)

theorem actual_lifted_cycle_isCycle {v : V} (c : G.Walk v v) (R : ℕ)
    (hc : c.IsCycle) : (LiftedCycle c R).IsCycle := by
  have he : (LiftedCycle c R).map (Embedding.induce _).toHom = c := by
    exact c.map_induce _
  rw [← he] at hc
  exact hc.of_map

theorem actual_lifted_cycle_length {v : V} (c : G.Walk v v) (R : ℕ) :
    (LiftedCycle c R).length = c.length := by
  have he : (LiftedCycle c R).map (Embedding.induce _).toHom = c := by
    exact c.map_induce _
  exact (Walk.length_map _ _).symm.trans (congrArg Walk.length he)

theorem actual_cycle_radius_induced_interior_degree [Fintype V] [DecidableEq V]
    {v : V} (c : G.Walk v v) (R : ℕ)
    (x : CycleRadius G c (R + 1)) (hx : x.val ∈ CycleRadius G c R) :
    (G.induce (CycleRadius G c (R + 1))).degree x = G.degree x.val := by
  apply degree_induce_of_neighborSet_subset
  intro y hy
  exact actual_cycle_radius_neighbors_closed c R hx hy

end Reference.MD06RadiusEmbedding
