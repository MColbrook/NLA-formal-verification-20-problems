module

public import NLA.MD06.CleanCycleGraph.GradientGeometry
public import NLA.MD06.CleanCycleGraph.CycleSigns

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile
attribute [local instance] Classical.propDecidable

theorem actual_child_zero_force {ell R : ℕ} (hR : 4 ≤ R) (x : TreeNodes ell R)
    (hx : x.1.val < R) : Real.sin (NodeProfile x-NodeProfile (ChildZero x hx)) =
      RootSign x.2.1 * Root R / (2 : ℝ)^x.1.val := by
  change Real.sin (RootSign x.2.1*Height R (Root R) x.1.val -
    RootSign x.2.1*Height R (Root R) (x.1.val+1)) = _
  rw [←mul_sub,actual_height_step hx,actual_root_sign_sine,
    actual_delta_sine (actual_root_spec hR).1]
  ring

theorem actual_child_one_force {ell R : ℕ} (hR : 4 ≤ R) (x : TreeNodes ell R)
    (h0 : 0 < x.1.val) (hx : x.1.val < R) :
    Real.sin (NodeProfile x-NodeProfile (ChildOne x h0 hx)) =
      RootSign x.2.1 * Root R / (2 : ℝ)^x.1.val := by
  change Real.sin (RootSign x.2.1*Height R (Root R) x.1.val -
    RootSign x.2.1*Height R (Root R) (x.1.val+1)) = _
  rw [←mul_sub,actual_height_step hx,actual_root_sign_sine,
    actual_delta_sine (actual_root_spec hR).1]
  ring

theorem actual_parent_force {ell R : ℕ} (hR : 4 ≤ R) (x : TreeNodes ell R)
    (h0 : 0 < x.1.val) : Real.sin (NodeProfile x-NodeProfile (ParentNode x h0)) =
      -RootSign x.2.1 * Root R / (2 : ℝ)^(x.1.val-1) := by
  change Real.sin (RootSign x.2.1*Height R (Root R) x.1.val -
    RootSign x.2.1*Height R (Root R) (x.1.val-1)) = _
  have hle := x.1.isLt
  have hj : x.1.val-1 < R := by omega
  have he : x.1.val-1+1 = x.1.val := by omega
  have hs := actual_height_step hj (Root R)
  rw [he] at hs
  have hr : Height R (Root R) x.1.val - Height R (Root R) (x.1.val-1) =
      -Delta (Root R) (x.1.val-1) := by linarith
  rw [←mul_sub,hr,mul_neg,Real.sin_neg,actual_root_sign_sine,
    actual_delta_sine (actual_root_spec hR).1]
  ring

theorem actual_parent_child_zero_distinct {ell R : ℕ} (x : TreeNodes ell R)
    (h0 : 0 < x.1.val) (hx : x.1.val < R) : ParentNode x h0 ≠ ChildZero x hx := by
  intro he
  have hd := congrArg (fun y : TreeNodes ell R => y.1.val) he
  change x.1.val-1 = x.1.val+1 at hd
  omega

theorem actual_parent_child_one_distinct {ell R : ℕ} (x : TreeNodes ell R)
    (h0 : 0 < x.1.val) (hx : x.1.val < R) : ParentNode x h0 ≠ ChildOne x h0 hx := by
  intro he
  have hd := congrArg (fun y : TreeNodes ell R => y.1.val) he
  change x.1.val-1 = x.1.val+1 at hd
  omega

theorem actual_children_distinct {ell R : ℕ} (x : TreeNodes ell R)
    (h0 : 0 < x.1.val) (hx : x.1.val < R) : ChildZero x hx ≠ ChildOne x h0 hx := by
  intro he
  have hb := congrArg (fun y : TreeNodes ell R => y.2.2.val) he
  change 2*x.2.2.val = 2*x.2.2.val+1 at hb
  omega

theorem actual_interior_tree_neighbor_force_zero {ell R : ℕ} (hR : 4 ≤ R)
    (x : TreeNodes ell R) (h0 : 0 < x.1.val) (hx : x.1.val < R) :
    (∑ y ∈ TreeNeighbors hR x, Real.sin (NodeProfile x-NodeProfile y)) = 0 := by
  have hp0 := actual_parent_child_zero_distinct x h0 hx
  have hp1 := actual_parent_child_one_distinct x h0 hx
  have hc := actual_children_distinct x h0 hx
  simp only [TreeNeighbors,dif_neg (Nat.ne_zero_of_lt h0),dif_pos hx]
  rw [Finset.sum_insert (by simp [hp0,hp1]),Finset.sum_insert (by simp [hc]),Finset.sum_singleton]
  rw [actual_parent_force hR,actual_child_zero_force hR,actual_child_one_force hR]
  have he : x.1.val = (x.1.val-1)+1 := by omega
  have hp : (2 : ℝ)^x.1.val = (2 : ℝ)^(x.1.val-1)*2 := by
    conv_lhs => rw [he,pow_succ]
  rw [hp]
  field_simp
  ring

theorem actual_embedded_interior_gradient_zero {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hR : 4 ≤ R) (e : CleanCycleEmbedding (ell := ell) G hR) (x : TreeNodes ell R)
    (h0 : 0 < x.1.val) (hx : x.1.val < R) :
    Gradient G (PhaseLift (fun v => EmbeddedProfile e.nodes v)) (e.nodes x) = 0 := by
  rw [actual_embedded_gradient_node_sum]
  exact actual_interior_tree_neighbor_force_zero hR x h0 hx
end Reference.MD06CleanCycle
