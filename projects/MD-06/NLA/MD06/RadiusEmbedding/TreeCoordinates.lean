module

public import NLA.MD06.RadiusEmbedding.RootFrames
public import NLA.MD06.CleanCycleGraph.TopologyDefinitions

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Reference.MD06RadiusEmbedding
open SimpleGraph
open Reference.MD06CleanCycle
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def TreeToRootBranch (ell R : ℕ) : TreeNodes ell R ≃ Fin ell × BranchNodes R where
  toFun x := ⟨x.2.1,⟨x.1,x.2.2⟩⟩
  invFun x := ⟨x.2.1,x.1,x.2.2⟩
  left_inv := by rintro ⟨j,i,b⟩; rfl
  right_inv := by rintro ⟨i,j,b⟩; rfl

noncomputable def RadiusTreeCoordinate {v : V} (c : G.Walk v v) (R : ℕ) (hR : 1 ≤ R)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3) :
    TreeNodes c.length R → CycleRadius G c R :=
  RootBranchCoordinate c R hR hc hcubic ∘ TreeToRootBranch c.length R

theorem actual_radius_tree_coordinate_bijective {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3) :
    Function.Bijective (RadiusTreeCoordinate c R hR hc hcubic) :=
  ⟨(actual_root_branch_coordinate_injective c R hR hc hcubic).comp
      (TreeToRootBranch c.length R).injective,
    (actual_root_branch_coordinate_surjective c R hR hc hcubic).comp
      (TreeToRootBranch c.length R).surjective⟩

noncomputable def ActualRadiusNodes {v : V} (c : G.Walk v v) (R : ℕ) (hR : 1 ≤ R)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3) : TreeNodes c.length R ↪ V where
  toFun x := (RadiusTreeCoordinate c R hR hc hcubic x).val
  inj' := Subtype.val_injective.comp (actual_radius_tree_coordinate_bijective c R hR hc hcubic).1

theorem actual_radius_nodes_range {v : V} (c : G.Walk v v) (R : ℕ) (hR : 1 ≤ R)
    (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3) :
    Set.range (ActualRadiusNodes c R hR hc hcubic) = CycleRadius G c R := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact (RadiusTreeCoordinate c R hR hc hcubic a).property
  · intro hx
    obtain ⟨a,ha⟩ := (actual_radius_tree_coordinate_bijective c R hR hc hcubic).2 ⟨x,hx⟩
    exact ⟨a,congrArg Subtype.val ha⟩

theorem actual_radius_tree_coordinate_reachable_distance {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x : TreeNodes c.length R) :
    (RadiusForest G c R).Reachable (RadiusCycleCoordinate c R hc x.2.1).val
      (RadiusTreeCoordinate c R hR hc hcubic x) ∧
    (RadiusForest G c R).dist (RadiusCycleCoordinate c R hc x.2.1).val
      (RadiusTreeCoordinate c R hR hc hcubic x) = x.1.val :=
  actual_radius_frame_reachable_distance c R hR hc hcubic _ _

theorem actual_radius_nodes_closed_interior {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x : TreeNodes c.length R) (hx : x.1.val < R) :
    G.neighborFinset (ActualRadiusNodes c R hR hc hcubic x) ⊆
      Finset.univ.image (ActualRadiusNodes c R hR hc hcubic) := by
  intro y hy
  have hcoord := actual_radius_tree_coordinate_reachable_distance c R hR hc hcubic x
  have hr := (RadiusCycleCoordinate c R hc x.2.1).property
  have hyR : y ∈ CycleRadius G c R := actual_radius_forest_closed_interior c R _ _
    (List.mem_toFinset.mp hr) hcoord.1 (by rw [hcoord.2]; exact hx)
    ((G.mem_neighborFinset _ _).mp hy)
  rw [← actual_radius_nodes_range c R hR hc hcubic] at hyR
  obtain ⟨a,ha⟩ := hyR
  exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha⟩

end Reference.MD06RadiusEmbedding
