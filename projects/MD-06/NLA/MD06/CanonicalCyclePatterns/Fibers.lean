module

public import NLA.MD06.CanonicalCyclePatterns.FiberDefinitions
public import NLA.MD06.CanonicalCyclePatterns.Determination

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06CanonicalCyclePatterns
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_canonical_cycle_dart_support_card {n ell : ℕ} (D : CycleData n ell) :
    (DartSupport (CanonicalCyclePattern D)).card=2*ell := by
  rw [CanonicalCyclePattern,actual_normalized_constraints_dart_support,
    actual_dart_support_card_of_disjoint _ (actual_cycle_pattern_distinct_endpoints D)
      (actual_cycle_pattern_disjoint_endpoints D),actual_cycle_pattern_card]

theorem actual_cycle_fiber_start_injective {n ell : ℕ} [NeZero ell]
    (C : Finset (Dart n × Dart n)) :
    Function.Injective (fun D : CycleFiber n ell C => incoming D.val 0) := by
  intro D E h
  apply Subtype.ext
  exact actual_cycle_start_determines D.val E.val (D.property.trans E.property.symm) h

theorem actual_canonical_cycle_fiber_card {n ell : ℕ} [NeZero ell]
    (C : CanonicalCycleDatum n ell) :
    Fintype.card (CycleFiber n ell C.val)=2*ell := by
  rcases C.property with ⟨D,hD⟩
  let f : Fin ell × Bool ↪ CycleFiber n ell C.val :=
    { toFun := fun z => ⟨SymmetryCycle D z,(actual_symmetry_cycle_pattern D z).trans hD⟩
      inj' := fun z w h => actual_symmetry_cycle_injective D (congrArg Subtype.val h) }
  have hlo : 2*ell ≤ Fintype.card (CycleFiber n ell C.val) := by
    simpa [Nat.mul_comm] using Fintype.card_le_of_injective f f.injective
  let g : CycleFiber n ell C.val ↪ {x : Dart n // x∈DartSupport C.val} :=
    { toFun := fun E => ⟨incoming E.val 0,by
        have hx : incoming E.val 0 ∈ DartSupport (CanonicalCyclePattern E.val) := by
          rw [CanonicalCyclePattern,actual_normalized_constraints_dart_support]
          exact (actual_mem_cycle_dart_support E.val _).mpr ⟨0,Or.inr rfl⟩
        exact (congrArg DartSupport E.property) ▸ hx⟩
      inj' := fun E F h => actual_cycle_fiber_start_injective C.val (congrArg Subtype.val h) }
  have hhi := Fintype.card_le_of_injective g g.injective
  rw [Fintype.card_coe] at hhi
  have hc : (DartSupport C.val).card=2*ell := by
    rw [←hD]
    exact actual_canonical_cycle_dart_support_card D
  rw [hc] at hhi
  exact Nat.le_antisymm hhi hlo

theorem actual_canonical_cycle_card_relation {n ell : ℕ} [NeZero ell] :
    Fintype.card (CycleData n ell)=
      (2*ell)*Fintype.card (CanonicalCycleDatum n ell) := by
  let e : CycleData n ell ≃
      (Σ C : CanonicalCycleDatum n ell, CycleFiber n ell C.val) :=
    { toFun := fun D => ⟨⟨CanonicalCyclePattern D,⟨D,rfl⟩⟩,⟨D,rfl⟩⟩
      invFun := fun X => X.2.val
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨C,D⟩
        apply Sigma.subtype_ext
        · exact Subtype.ext D.property
        · rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma] at h
  calc
    Fintype.card (CycleData n ell) =
        ∑ C : CanonicalCycleDatum n ell, Fintype.card (CycleFiber n ell C.val) := h
    _ = ∑ _ : CanonicalCycleDatum n ell, 2*ell := by
      apply Finset.sum_congr rfl
      intro C hC
      exact actual_canonical_cycle_fiber_card C
    _ = (2*ell)*Fintype.card (CanonicalCycleDatum n ell) := by simp [Nat.mul_comm]

#print axioms actual_canonical_cycle_dart_support_card
#print axioms actual_cycle_fiber_start_injective
#print axioms actual_canonical_cycle_fiber_card
#print axioms actual_canonical_cycle_card_relation
end Reference.MD06CanonicalCyclePatterns
