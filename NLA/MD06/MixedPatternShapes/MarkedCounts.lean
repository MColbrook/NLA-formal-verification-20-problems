module

public import NLA.MD06.MixedPatternShapes.FiniteShapes
public import NLA.MD06.BadSupportEnumeration.Cardinality
public import NLA.MD06.BadSupportEnumeration.JointCounts

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedPatternShapes
open Reference.MD06CubicConfiguration Reference.MD06CyclePairPatterns
open Reference.MD06CanonicalCyclePatterns Reference.MD06JointSupportCounts
open Reference.MD06Simplicity Reference.MD06SupportedCanonicalCycles
open Reference.MD06BadSupportEnumeration
attribute [local instance] Classical.propDecidable

theorem actual_supported_marked_card_bound {n ell : ℕ} (S : Finset (Fin n)) :
    Fintype.card (SupportedMarked S ell)≤3*S.card+18*S.card^2+2^(9*S.card^2) := by
  let e : SupportedMarked S ell ≃
      SupportedBadDatum n S⊕SupportedCanonicalCycle S ell :=
    { toFun := fun d => match d with
        | ⟨.inl b,h⟩ => .inl ⟨b,h⟩
        | ⟨.inr C,h⟩ => .inr ⟨C,h⟩
      invFun := fun d => match d with
        | .inl b => ⟨.inl b.val,b.property⟩
        | .inr C => ⟨.inr C.val,C.property⟩
      left_inv := by rintro ⟨b,h⟩;cases b <;> rfl
      right_inv := by intro b;cases b <;> rfl }
  rw [Fintype.card_congr e,Fintype.card_sum]
  exact Nat.add_le_add (actual_supported_bad_card_le S) (actual_supported_canonical_shape_bound S)

theorem actual_supported_marked_component {n q ell : ℕ} (S : Finset (Fin n))
    (F : SupportedMarkedTuple S q ell) (i : Fin q) :
    VertexSupport (MarkedPattern (F.val i))⊆S := by
  apply Finset.Subset.trans _ F.property
  apply actual_vertex_support_mono
  intro e he
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,he⟩

theorem actual_supported_marked_tuple_card_bound {n q ell : ℕ} (S : Finset (Fin n)) :
    Fintype.card (SupportedMarkedTuple S q ell)≤
      (3*S.card+18*S.card^2+2^(9*S.card^2))^q := by
  let f : SupportedMarkedTuple S q ell→Fin q→SupportedMarked S ell :=
    fun F i => ⟨F.val i,actual_supported_marked_component S F i⟩
  have hf : Function.Injective f := by
    intro F G h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  calc
    Fintype.card (SupportedMarkedTuple S q ell)≤
        Fintype.card (Fin q→SupportedMarked S ell) := Fintype.card_le_of_injective f hf
    _ = (Fintype.card (SupportedMarked S ell))^q := by simp
    _ ≤ (3*S.card+18*S.card^2+2^(9*S.card^2))^q :=
      Nat.pow_le_pow_left (actual_supported_marked_card_bound S) q

#print axioms actual_supported_marked_card_bound
#print axioms actual_supported_marked_component
#print axioms actual_supported_marked_tuple_card_bound
end Reference.MD06MixedPatternShapes
