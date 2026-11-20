module

public import NLA.MD06.CleanCycleGraph.RootLeafForces

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CleanCycle
open Reference.MD06Actual Reference.MD06Correction Reference.MD06CycleProfile
attribute [local instance] Classical.propDecidable

theorem actual_embedded_opposite_roots_force {n ell R : ℕ} (hell : 4 ≤ ell)
    (e : TreeNodes ell R ↪ Fin n) (hR : 4 ≤ R) :
    (1/2 : ℝ) < |Real.sin (EmbeddedProfile e (e (RootNode (R := R) ⟨1,by omega⟩))-
      EmbeddedProfile e (e (RootNode (R := R) ⟨2,by omega⟩)))| := by
  rw [actual_embedded_profile_at_node,actual_embedded_profile_at_node]
  have he : NodeProfile (RootNode (R := R) (⟨1,by omega⟩ : Fin ell))-
      NodeProfile (RootNode (R := R) (⟨2,by omega⟩ : Fin ell)) = 2*Height R (Root R) 0 := by
    have h1 : NodeProfile (RootNode (R := R) (⟨1,by omega⟩ : Fin ell)) = Height R (Root R) 0 := by
      change RootSign (⟨1,by omega⟩ : Fin ell)*Height R (Root R) 0 = _
      norm_num [RootSign]
    have h2 : NodeProfile (RootNode (R := R) (⟨2,by omega⟩ : Fin ell)) = -Height R (Root R) 0 := by
      change RootSign (⟨2,by omega⟩ : Fin ell)*Height R (Root R) 0 = _
      norm_num [RootSign]
    rw [h1,h2]
    ring
  rw [he]
  exact actual_profile_opposite_root_sine_gt_half hR

theorem actual_embedded_opposite_roots_distinct {n ell R : ℕ} (hell : 4 ≤ ell)
    (e : TreeNodes ell R ↪ Fin n) :
    e (RootNode (R := R) (⟨1,by omega⟩ : Fin ell)) ≠ e (RootNode (R := R) (⟨2,by omega⟩ : Fin ell)) := by
  intro he
  have hi := actual_root_node_injective (e.injective he)
  have hv := congrArg Fin.val hi
  norm_num at hv

theorem actual_clean_embedding_dimension {n ell R : ℕ} (e : TreeNodes ell R ↪ Fin n) : ell ≤ n := by
  have h := Fintype.card_le_of_injective (e ∘ RootNode (ell := ell) (R := R)) (e.injective.comp (actual_root_node_injective (ell := ell) (R := R)))
  simpa using h
end Reference.MD06CleanCycle
