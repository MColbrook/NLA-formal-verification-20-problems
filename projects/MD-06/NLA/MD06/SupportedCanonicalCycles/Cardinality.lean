module

public import NLA.MD06.SupportedCanonicalCycles.SupportProperties
public import NLA.MD06.CanonicalCyclePatterns.Fibers
public import NLA.MD06.CyclePairPatterns.FirstMoment

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06SupportedCanonicalCycles
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
attribute [local instance] Classical.propDecidable

theorem actual_supported_raw_cycle_card {n ell : ℕ} (S : Finset (Fin n)) :
    Fintype.card (SupportedRawCycle S ell)=S.card.descFactorial ell*6^ell := by
  let e : SupportedRawCycle S ell ≃ ((Fin ell↪↥S)×CycleAssignment ell) :=
    { toFun := fun D =>
        ({ toFun := fun i => ⟨D.val.1 i,D.property i⟩
           inj' := fun i j h => D.val.1.injective (congrArg Subtype.val h) },D.val.2)
      invFun := fun X =>
        ⟨({ toFun := fun i => (X.1 i).val
            inj' := fun i j h => X.1.injective (Subtype.ext h) },X.2),
          fun i => (X.1 i).property⟩
      left_inv := by rintro ⟨⟨f,a⟩,h⟩;rfl
      right_inv := by rintro ⟨f,a⟩;rfl }
  rw [Fintype.card_congr e,Fintype.card_prod,actual_cycle_assignment_card,
    Fintype.card_embedding_eq,Fintype.card_coe,Fintype.card_fin]

theorem actual_supported_canonical_cycle_card_relation {n ell : ℕ} [NeZero ell]
    (S : Finset (Fin n)) :
    Fintype.card (SupportedRawCycle S ell)=
      (2*ell)*Fintype.card (SupportedCanonicalCycle S ell) := by
  let e : SupportedRawCycle S ell ≃
      (Σ C : SupportedCanonicalCycle S ell,CycleFiber n ell C.val.val) :=
    { toFun := fun D =>
        ⟨⟨⟨CanonicalCyclePattern D.val,⟨D.val,rfl⟩⟩,
          (actual_raw_cycle_support_iff S D.val).mp D.property⟩,⟨D.val,rfl⟩⟩
      invFun := fun X => ⟨X.2.val,actual_supported_canonical_fiber_raw S X.1 X.2⟩
      left_inv := by rintro ⟨D,hD⟩;rfl
      right_inv := by
        rintro ⟨C,D⟩
        apply Sigma.subtype_ext
        · apply Subtype.ext
          exact Subtype.ext D.property
        · rfl }
  have h := Fintype.card_congr e
  rw [Fintype.card_sigma] at h
  calc
    Fintype.card (SupportedRawCycle S ell) =
        ∑ C : SupportedCanonicalCycle S ell,Fintype.card (CycleFiber n ell C.val.val) := h
    _ = ∑ _ : SupportedCanonicalCycle S ell,2*ell := by
      apply Finset.sum_congr rfl
      intro C hC
      exact actual_canonical_cycle_fiber_card C.val
    _ = (2*ell)*Fintype.card (SupportedCanonicalCycle S ell) := by simp [Nat.mul_comm]

theorem actual_supported_canonical_cycle_card {n ell : ℕ} [NeZero ell]
    (S : Finset (Fin n)) :
    (2*ell)*Fintype.card (SupportedCanonicalCycle S ell)=
      S.card.descFactorial ell*6^ell := by
  rw [←actual_supported_canonical_cycle_card_relation,actual_supported_raw_cycle_card]

#print axioms actual_supported_raw_cycle_card
#print axioms actual_supported_canonical_cycle_card_relation
#print axioms actual_supported_canonical_cycle_card
end Reference.MD06SupportedCanonicalCycles
