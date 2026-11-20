module

public import NLA.MD06.CleanCycleGraph.TreeForces

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile
attribute [local instance] Classical.propDecidable

theorem actual_root_node_injective {ell R : ℕ} : Function.Injective (RootNode (ell := ell) (R := R)) := by
  intro i j he
  exact congrArg (fun x : TreeNodes ell R => x.2.1) he

theorem actual_cycle_next_previous_distinct {ell : ℕ} (hell : 4 ≤ ell) (hdiv : 4 ∣ ell)
    (i : Fin ell) : NextRoot i ≠ PreviousRoot i := by
  intro he
  have hs := actual_cycle_neighbor_signs_opposite hell hdiv i
  have heq := congrArg RootSign he
  have hsq := actual_root_sign_square (NextRoot i)
  nlinarith

theorem actual_root_child_distinct {ell R : ℕ} (i j : Fin ell) (hR : 4 ≤ R) :
    RootNode (R := R) i ≠ ChildZero (RootNode (R := R) j) (by change 0 < R; omega) := by
  intro he
  have hd := congrArg (fun x : TreeNodes ell R => x.1.val) he
  change 0 = 1 at hd
  omega

theorem actual_root_neighbor_force_zero {ell R : ℕ} (hell : 4 ≤ ell) (hdiv : 4 ∣ ell)
    (hR : 4 ≤ R) (i : Fin ell) :
    (∑ y ∈ TreeNeighbors hR (RootNode (R := R) i),
      Real.sin (NodeProfile (RootNode (R := R) i)-NodeProfile y)) = 0 := by
  have hn : RootNode (R := R) (NextRoot i) ≠ RootNode (R := R) (PreviousRoot i) :=
    fun he => actual_cycle_next_previous_distinct hell hdiv i (actual_root_node_injective he)
  have hnc := actual_root_child_distinct (NextRoot i) i hR
  have hpc := actual_root_child_distinct (PreviousRoot i) i hR
  change (∑ y ∈ {RootNode (R := R) (NextRoot i),RootNode (R := R) (PreviousRoot i),
    ChildZero (RootNode (R := R) i) (by change 0 < R; omega)},
    Real.sin (NodeProfile (RootNode (R := R) i)-NodeProfile y)) = 0
  rw [Finset.sum_insert (by simp [hn,hnc]),Finset.sum_insert (by simp [hpc]),Finset.sum_singleton]
  rw [←add_assoc,actual_cycle_two_neighbor_force hell hdiv hR,actual_child_zero_force hR]
  simp [RootNode]

theorem actual_embedded_root_gradient_zero {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hell : 4 ≤ ell) (hdiv : 4 ∣ ell) (hR : 4 ≤ R)
    (e : CleanCycleEmbedding (ell := ell) G hR) (i : Fin ell) :
    Gradient G (PhaseLift (fun v => EmbeddedProfile e.nodes v)) (e.nodes (RootNode i)) = 0 := by
  rw [actual_embedded_gradient_node_sum]
  exact actual_root_neighbor_force_zero hell hdiv hR i

theorem actual_embedded_leaf_gradient {n ell R : ℕ} (G : SimpleGraph (Fin n))
    (hR : 4 ≤ R) (e : CleanCycleEmbedding (ell := ell) G hR) (x : TreeNodes ell R)
    (hx : x.1.val = R) :
    Gradient G (PhaseLift (fun v => EmbeddedProfile e.nodes v)) (e.nodes x) =
      -RootSign x.2.1 * Root R / (2 : ℝ)^(R-1) := by
  have h0 : 0 < x.1.val := by omega
  have hnot : ¬x.1.val < R := by omega
  rw [actual_embedded_gradient_node_sum]
  simp only [TreeNeighbors,dif_neg (Nat.ne_zero_of_lt h0),dif_neg hnot,Finset.sum_singleton]
  rw [actual_parent_force hR]
  have he : (2 : ℝ)^(x.1.val-1) = (2 : ℝ)^(R-1) := by rw [hx]
  rw [he]
end Reference.MD06CleanCycle
