module

public import NLA.MD06.CleanCycleGraph.TopologyDefinitions
public import NLA.MD06.CleanCycleGraph.LevelCounts

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open scoped BigOperators
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile

theorem actual_embedded_profile_at_node {n ell R : ℕ} (e : TreeNodes ell R ↪ Fin n)
    (x : TreeNodes ell R) : EmbeddedProfile e (e x) = NodeProfile x := by
  change Function.extend e (NodeProfile (ell := ell) (R := R)) (fun _ : Fin n => 0) (e x) = NodeProfile x
  exact e.injective.extend_apply _ _ x

theorem actual_embedded_profile_outside {n ell R : ℕ} (e : TreeNodes ell R ↪ Fin n)
    (v : Fin n) (hv : v ∉ Set.range e) : EmbeddedProfile e v = 0 := by
  change Function.extend e (NodeProfile (ell := ell) (R := R)) (fun _ : Fin n => 0) v = 0
  exact Function.extend_apply' _ _ v hv

theorem actual_embedded_leaf_profile_zero {n ell R : ℕ} (e : TreeNodes ell R ↪ Fin n)
    (x : TreeNodes ell R) (hx : x.1.val = R) : EmbeddedProfile e (e x) = 0 := by
  rw [actual_embedded_profile_at_node]
  have hh : Height R (Root R) x.1.val = 0 := by rw [hx,actual_height_terminal]
  simp [NodeProfile,hh]
end Reference.MD06CleanCycle
