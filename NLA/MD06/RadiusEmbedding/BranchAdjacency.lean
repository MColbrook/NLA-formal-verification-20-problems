module

public import NLA.MD06.RadiusEmbedding.TreeCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Reference.MD06RadiusEmbedding
open SimpleGraph
open Reference.MD06CleanCycle
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

set_option linter.unnecessarySeqFocus false in
theorem actual_frame_value_parent_adj (hG : G.IsAcyclic) (root : V) (R : ℕ)
    (hroot : G.degree root = 1)
    (hinterior : ∀ v, G.Reachable root v → 0 < G.dist root v →
      G.dist root v < R → G.degree v = 3)
    (j : ℕ) (hj : 1 ≤ j) (hjR : j ≤ R) (b : Fin (2 ^ (j-1))) :
    G.Adj
      (FrameValue hG root R hroot hinterior
        ⟨⟨j-1,by omega⟩,⟨b.val/2,parent_index_lt (by omega) b.isLt⟩⟩)
      (FrameValue hG root R hroot hinterior ⟨⟨j,by omega⟩,b⟩) := by
  by_cases h1 : j = 1
  · subst j
    change G.Adj root (BinaryFrames hG root R hroot hinterior 1 (by omega) hjR b).val
    exact actual_binary_frames_one_adj hG root R hroot hinterior hjR b
  · have h2 : 2 ≤ j := by omega
    simp only [FrameValue, dif_neg (show j-1 ≠ 0 by omega), dif_neg (show j ≠ 0 by omega)]
    have hadj := actual_binary_frames_parent_adj hG root R hroot hinterior
      (j-1) (by omega) (by omega) b
    convert hadj using 1 <;> congr! 4 <;> omega

theorem actual_radius_tree_parent_adj {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x : TreeNodes c.length R) (h0 : 0 < x.1.val) :
    (RadiusForest G c R).Adj
      (RadiusTreeCoordinate c R hR hc hcubic (ParentNode x h0))
      (RadiusTreeCoordinate c R hR hc hcubic x) := by
  unfold RadiusTreeCoordinate RootBranchCoordinate TreeToRootBranch
  dsimp only [Function.comp_apply, Equiv.coe_fn_mk]
  unfold RadiusFrame
  exact actual_frame_value_parent_adj _ _ _ _ _ x.1.val (by omega)
    (by have hx := x.1.isLt; omega) x.2.2

theorem actual_parent_child_zero {ell R : ℕ} (x : TreeNodes ell R) (hx : x.1.val < R) :
    ParentNode (ChildZero x hx) (by simp [ChildZero]) = x := by
  rcases x with ⟨j,i,b⟩
  apply Sigma.ext
  · apply Fin.ext
    simp only [ParentNode,ChildZero,Nat.add_sub_cancel]
  · apply heq_of_eq
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [ParentNode,ChildZero,Nat.mul_div_cancel_left _ (show 0 < 2 by omega)]

theorem actual_parent_child_one {ell R : ℕ} (x : TreeNodes ell R)
    (h0 : 0 < x.1.val) (hx : x.1.val < R) :
    ParentNode (ChildOne x h0 hx) (by simp [ChildOne]) = x := by
  rcases x with ⟨j,i,b⟩
  apply Sigma.ext
  · apply Fin.ext
    simp only [ParentNode,ChildOne,Nat.add_sub_cancel]
  · apply heq_of_eq
    apply Prod.ext
    · rfl
    · apply Fin.ext
      simp only [ParentNode,ChildOne]
      omega

theorem actual_radius_tree_child_zero_adj {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x : TreeNodes c.length R) (hx : x.1.val < R) :
    (RadiusForest G c R).Adj
      (RadiusTreeCoordinate c R hR hc hcubic x)
      (RadiusTreeCoordinate c R hR hc hcubic (ChildZero x hx)) := by
  have h := actual_radius_tree_parent_adj c R hR hc hcubic (ChildZero x hx)
    (by simp [ChildZero])
  rwa [actual_parent_child_zero] at h

theorem actual_radius_tree_child_one_adj {v : V} (c : G.Walk v v)
    (R : ℕ) (hR : 1 ≤ R) (hc : CleanRadius G c R) (hcubic : ∀ x, G.degree x = 3)
    (x : TreeNodes c.length R) (h0 : 0 < x.1.val) (hx : x.1.val < R) :
    (RadiusForest G c R).Adj
      (RadiusTreeCoordinate c R hR hc hcubic x)
      (RadiusTreeCoordinate c R hR hc hcubic (ChildOne x h0 hx)) := by
  have h := actual_radius_tree_parent_adj c R hR hc hcubic (ChildOne x h0 hx)
    (by simp [ChildOne])
  rwa [actual_parent_child_one] at h

end Reference.MD06RadiusEmbedding
