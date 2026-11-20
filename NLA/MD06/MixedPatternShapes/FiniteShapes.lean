module

public import NLA.MD06.MixedPatternShapes.Definitions
public import NLA.MD06.JointSupportCounts.SupportProperties
public import Mathlib.Data.Finset.Powerset

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedPatternShapes
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06Simplicity Reference.MD06SupportedCanonicalCycles
attribute [local instance] Classical.propDecidable

theorem actual_local_darts_card {n : ℕ} (S : Finset (Fin n)) :
    (LocalDarts S).card=3*S.card := by
  simp only [LocalDarts,Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_fin]
  ring

theorem actual_local_edges_card {n : ℕ} (S : Finset (Fin n)) :
    (LocalEdges S).card=9*S.card^2 := by
  rw [LocalEdges,Finset.product_eq_sprod,Finset.card_product,actual_local_darts_card]
  ring

theorem actual_constraint_support_iff {n : ℕ} (S : Finset (Fin n))
    (C : Finset (Dart n×Dart n)) :
    VertexSupport C⊆S ↔ C⊆LocalEdges S := by
  constructor
  · intro h e he
    have h1 : e.1.1∈S := h ((actual_mem_vertex_support C e.1.1).mpr
      ⟨e.1.2,(actual_mem_dart_support C e.1).mpr ⟨e,he,Or.inl rfl⟩⟩)
    have h2 : e.2.1∈S := h ((actual_mem_vertex_support C e.2.1).mpr
      ⟨e.2.2,(actual_mem_dart_support C e.2).mpr ⟨e,he,Or.inr rfl⟩⟩)
    exact Finset.mem_product.mpr
      ⟨Finset.mem_product.mpr ⟨h1,Finset.mem_univ _⟩,
        Finset.mem_product.mpr ⟨h2,Finset.mem_univ _⟩⟩
  · intro h u hu
    rcases (actual_mem_vertex_support C u).mp hu with ⟨a,ha⟩
    rcases (actual_mem_dart_support C (u,a)).mp ha with ⟨e,he,hx⟩
    have he' := Finset.mem_product.mp (h he)
    rcases hx with hx | hx
    · have hh : u=e.1.1 := congrArg Prod.fst hx
      exact hh ▸ (Finset.mem_product.mp he'.1).1
    · have hh : u=e.2.1 := congrArg Prod.fst hx
      exact hh ▸ (Finset.mem_product.mp he'.2).1

theorem actual_supported_constraint_card {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (ConstraintOn S)=2^(9*S.card^2) := by
  let e : ConstraintOn S ≃ ↥(LocalEdges S).powerset :=
    { toFun := fun C => ⟨C.val,Finset.mem_powerset.mpr
        ((actual_constraint_support_iff S C.val).mp C.property)⟩
      invFun := fun C => ⟨C.val,(actual_constraint_support_iff S C.val).mpr
        (Finset.mem_powerset.mp C.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e,Fintype.card_coe,Finset.card_powerset,actual_local_edges_card]

theorem actual_supported_canonical_shape_bound {n ell : ℕ} (S : Finset (Fin n)) :
    Fintype.card (SupportedCanonicalCycle S ell)≤2^(9*S.card^2) := by
  let f : SupportedCanonicalCycle S ell→ConstraintOn S :=
    fun C => ⟨C.val.val,C.property⟩
  have hf : Function.Injective f := by
    intro C D h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ConstraintOn S => z.val) h
  exact (Fintype.card_le_of_injective f hf).trans (le_of_eq (actual_supported_constraint_card S))

#print axioms actual_local_darts_card
#print axioms actual_local_edges_card
#print axioms actual_constraint_support_iff
#print axioms actual_supported_constraint_card
#print axioms actual_supported_canonical_shape_bound
end Reference.MD06MixedPatternShapes
