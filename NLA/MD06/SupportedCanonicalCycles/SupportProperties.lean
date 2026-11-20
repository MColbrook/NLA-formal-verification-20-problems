module

public import NLA.MD06.SupportedCanonicalCycles.Definitions
public import NLA.MD06.CanonicalCyclePatterns.CycleSupport

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06SupportedCanonicalCycles
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_raw_cycle_support_iff {n ell : ℕ} (S : Finset (Fin n))
    (D : CycleData n ell) :
    (∀i : Fin ell,D.1 i∈S) ↔ VertexSupport (CanonicalCyclePattern D)⊆S := by
  rw [actual_canonical_cycle_vertex_support]
  constructor
  · intro h u hu
    rcases Finset.mem_image.mp hu with ⟨i,hi,he⟩
    exact he ▸ h i
  · intro h i
    exact h (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)

theorem actual_supported_canonical_fiber_raw {n ell : ℕ} (S : Finset (Fin n))
    (C : SupportedCanonicalCycle S ell) (D : CycleFiber n ell C.val.val) :
    ∀i : Fin ell,D.val.1 i∈S := by
  apply (actual_raw_cycle_support_iff S D.val).mpr
  rw [D.property]
  exact C.property

theorem actual_supported_cycle_vertex_card {n ell : ℕ} (S : Finset (Fin n))
    (C : SupportedCanonicalCycle S ell) :
    (VertexSupport C.val.val).card=ell := by
  rcases C.val.property with ⟨D,hD⟩
  rw [←hD,actual_canonical_cycle_vertex_support,
    Finset.card_image_of_injective _ D.1.injective]
  exact Fintype.card_fin ell

theorem actual_supported_cycle_length_le {n ell : ℕ} (S : Finset (Fin n))
    (C : SupportedCanonicalCycle S ell) : ell≤S.card := by
  rw [←actual_supported_cycle_vertex_card S C]
  exact Finset.card_le_card C.property

#print axioms actual_raw_cycle_support_iff
#print axioms actual_supported_canonical_fiber_raw
#print axioms actual_supported_cycle_vertex_card
#print axioms actual_supported_cycle_length_le
end Reference.MD06SupportedCanonicalCycles
