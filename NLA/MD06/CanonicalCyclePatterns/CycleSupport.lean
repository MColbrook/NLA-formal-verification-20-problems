module

public import NLA.MD06.CanonicalCyclePatterns.Normalization

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_mem_cycle_dart_support {n ell : ℕ} (D : CycleData n ell) (x : Dart n) :
    x ∈ DartSupport (CyclePattern D) ↔
      ∃ i : Fin ell, x = outgoing D i ∨ x = incoming D i := by
  constructor
  · intro hx
    rcases (actual_mem_dart_support (CyclePattern D) x).mp hx with ⟨e,he,hx⟩
    rcases Finset.mem_image.mp he with ⟨i,hi,heq⟩
    subst e
    rcases hx with h | h
    · exact ⟨i,Or.inl h⟩
    · exact ⟨finRotate ell i,Or.inr h⟩
  · rintro ⟨i,hi | hi⟩
    · exact (actual_mem_dart_support (CyclePattern D) x).mpr
        ⟨cycleEdge D i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,Or.inl hi⟩
    · let j : Fin ell := (finRotate ell).symm i
      apply (actual_mem_dart_support (CyclePattern D) x).mpr
      refine ⟨cycleEdge D j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,Or.inr ?_⟩
      simpa only [cycleEdge,j,Equiv.apply_symm_apply] using hi

theorem actual_cycle_vertex_support {n ell : ℕ} (D : CycleData n ell) :
    VertexSupport (CyclePattern D) = Finset.univ.image D.1 := by
  ext u
  rw [actual_mem_vertex_support]
  constructor
  · rintro ⟨a,ha⟩
    rcases (actual_mem_cycle_dart_support D (u,a)).mp ha with ⟨i,hi | hi⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,(congrArg Prod.fst hi).symm⟩
    · exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,(congrArg Prod.fst hi).symm⟩
  · intro hu
    rcases Finset.mem_image.mp hu with ⟨i,hi,heq⟩
    subst u
    exact ⟨(D.2 i).val.2,(actual_mem_cycle_dart_support D _).mpr
      ⟨i,Or.inl rfl⟩⟩

theorem actual_cycle_vertex_support_card {n ell : ℕ} (D : CycleData n ell) :
    (VertexSupport (CyclePattern D)).card = ell := by
  rw [actual_cycle_vertex_support,Finset.card_image_of_injective _ D.1.injective]
  exact Fintype.card_fin ell

theorem actual_cycle_local_support {n ell : ℕ} (D : CycleData n ell) (i : Fin ell) :
    LocalSupport (CyclePattern D) (D.1 i) = {(D.2 i).val.1,(D.2 i).val.2} := by
  ext a
  rw [actual_mem_local_support,actual_mem_cycle_dart_support]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨j,hj | hj⟩
    · have hij : i=j := D.1.injective (congrArg Prod.fst hj)
      subst j
      exact Or.inr (congrArg Prod.snd hj)
    · have hij : i=j := D.1.injective (congrArg Prod.fst hj)
      subst j
      exact Or.inl (congrArg Prod.snd hj)
  · rintro (h | h)
    · exact ⟨i,Or.inr (Prod.ext rfl h)⟩
    · exact ⟨i,Or.inl (Prod.ext rfl h)⟩

theorem actual_cycle_local_support_card {n ell : ℕ} (D : CycleData n ell) (i : Fin ell) :
    (LocalSupport (CyclePattern D) (D.1 i)).card = 2 := by
  rw [actual_cycle_local_support]
  simp [(D.2 i).property]

theorem actual_canonical_cycle_vertex_support {n ell : ℕ} (D : CycleData n ell) :
    VertexSupport (CanonicalCyclePattern D) = Finset.univ.image D.1 := by
  rw [CanonicalCyclePattern,actual_normalized_constraints_vertex_support,
    actual_cycle_vertex_support]

theorem actual_canonical_cycle_local_support {n ell : ℕ} (D : CycleData n ell)
    (i : Fin ell) :
    LocalSupport (CanonicalCyclePattern D) (D.1 i) =
      {(D.2 i).val.1,(D.2 i).val.2} := by
  ext a
  rw [actual_mem_local_support,CanonicalCyclePattern,
    actual_normalized_constraints_dart_support,←actual_mem_local_support,
    actual_cycle_local_support]

#print axioms actual_mem_cycle_dart_support
#print axioms actual_cycle_vertex_support
#print axioms actual_cycle_vertex_support_card
#print axioms actual_cycle_local_support
#print axioms actual_cycle_local_support_card
#print axioms actual_canonical_cycle_vertex_support
#print axioms actual_canonical_cycle_local_support
end Reference.MD06CanonicalCyclePatterns
