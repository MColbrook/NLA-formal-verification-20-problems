module

public import NLA.MD06.RadiusEmbedding.RadiusCoverage

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Reference.MD06RadiusEmbedding
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

noncomputable def RadiusCycleCoordinate {v : V} (c : G.Walk v v) (R : ℕ)
    (hc : CleanRadius G c R) :
    Fin c.length ≃ (LiftedCycle c R).support.toFinset :=
  (finCongr (actual_lifted_cycle_length c R).symm).trans
    (CycleRootCoordinate (LiftedCycle c R) hc.1)

omit [Fintype V] [DecidableEq V] in
theorem RadiusAcyclic {v : V} (c : G.Walk v v) (R : ℕ)
    (hc : CleanRadius G c R) : (RadiusForest G c R).IsAcyclic :=
  actual_unique_cycle_deletion_forest (LiftedCycle c R) hc

theorem actual_radius_root_degree {v : V} (c : G.Walk v v) (R : ℕ) (hR : 1 ≤ R)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (r : (LiftedCycle c R).support.toFinset) : (RadiusForest G c R).degree r.val = 1 := by
  convert! actual_clean_radius_root_forest_degree_one c R hR hc hcubic r.val
    (List.mem_toFinset.mp r.property) using 1

theorem actual_radius_interior_degree {v : V} (c : G.Walk v v) (R : ℕ)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (r : (LiftedCycle c R).support.toFinset) (x : CycleRadius G c R)
    (hx : (RadiusForest G c R).Reachable r.val x)
    (hp : 0 < (RadiusForest G c R).dist r.val x)
    (hlt : (RadiusForest G c R).dist r.val x < R) :
    (RadiusForest G c R).degree x = 3 := by
  convert! actual_clean_radius_interior_forest_degree_three c R hc hcubic r.val x
    (List.mem_toFinset.mp r.property) hx hp hlt using 1

noncomputable def RadiusFrame {v : V} (c : G.Walk v v) (R : ℕ) (hR : 1 ≤ R)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (r : (LiftedCycle c R).support.toFinset) : BranchNodes R → CycleRadius G c R :=
  FrameValue (RadiusAcyclic c R hc) r.val R
    (by
      convert! actual_radius_root_degree c R hR hc hcubic r using 1
      unfold SimpleGraph.degree
      congr 1
      ext y
      simp only [mem_neighborFinset])
    (by
      intro x hx hp hlt
      convert! actual_radius_interior_degree c R hc hcubic r x hx hp hlt using 1
      unfold SimpleGraph.degree
      congr 1
      ext y
      simp only [mem_neighborFinset])

theorem actual_radius_frame_reachable_distance {v : V} (c : G.Walk v v) (R : ℕ)
    (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (r : (LiftedCycle c R).support.toFinset) (x : BranchNodes R) :
    (RadiusForest G c R).Reachable r.val (RadiusFrame c R hR hc hcubic r x) ∧
      (RadiusForest G c R).dist r.val (RadiusFrame c R hR hc hcubic r x) = x.1.val :=
  actual_frame_value_reachable_distance _ _ _ _ _ _

theorem actual_radius_frame_injective {v : V} (c : G.Walk v v) (R : ℕ)
    (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (r : (LiftedCycle c R).support.toFinset) :
    Function.Injective (RadiusFrame c R hR hc hcubic r) :=
  actual_frame_value_injective _ _ _ _ _

noncomputable def RootBranchCoordinate {v : V} (c : G.Walk v v) (R : ℕ) (hR : 1 ≤ R)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3) :
    Fin c.length × BranchNodes R → CycleRadius G c R :=
  fun x => RadiusFrame c R hR hc hcubic (RadiusCycleCoordinate c R hc x.1) x.2

theorem actual_root_branch_coordinate_injective {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3) :
    Function.Injective (RootBranchCoordinate c R hR hc hcubic) := by
  intro x y heq
  let r := RadiusCycleCoordinate c R hc x.1
  let s := RadiusCycleCoordinate c R hc y.1
  have hx := actual_radius_frame_reachable_distance c R hR hc hcubic r x.2
  have hy := actual_radius_frame_reachable_distance c R hR hc hcubic s y.2
  change RadiusFrame c R hR hc hcubic r x.2 = RadiusFrame c R hR hc hcubic s y.2 at heq
  have hr : r.val = s.val := actual_unique_cycle_forest_roots_separated
    (LiftedCycle c R) hc (actual_cycle_radius_induced_connected c R)
    (List.mem_toFinset.mp r.property) (List.mem_toFinset.mp s.property)
    (hx.1.trans (heq ▸ hy.1).symm)
  have hi : x.1 = y.1 := (RadiusCycleCoordinate c R hc).injective (Subtype.ext hr)
  rcases x with ⟨i,a⟩
  rcases y with ⟨j,b⟩
  dsimp at hi
  subst j
  apply Prod.ext
  · rfl
  · exact actual_radius_frame_injective c R hR hc hcubic _ heq

theorem actual_root_branch_coordinate_surjective {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3) :
    Function.Surjective (RootBranchCoordinate c R hR hc hcubic) := by
  intro x
  obtain ⟨r,hr,hrx,hd⟩ := actual_radius_forest_bounded_root c R x
  let s : (LiftedCycle c R).support.toFinset := ⟨r,List.mem_toFinset.mpr hr⟩
  have hframe : ∃ a : BranchNodes R, RadiusFrame c R hR hc hcubic s a = x := by
    unfold RadiusFrame
    exact actual_frame_value_surjective_truncation _ _ _ _ _ x hrx hd
  obtain ⟨a,ha⟩ := hframe
  refine ⟨⟨(RadiusCycleCoordinate c R hc).symm s,a⟩,?_⟩
  unfold RootBranchCoordinate
  rw [Equiv.apply_symm_apply]
  exact ha

end Reference.MD06RadiusEmbedding
