module

public import NLA.MD06.BadSupportEnumeration.Definitions
public import NLA.MD06.JointSupportCounts.BadSupport
public import NLA.MD06.BadPatternCounts.Cardinality

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06BadSupportEnumeration
open Reference.MD06Simplicity Reference.MD06CubicConfiguration
open Reference.MD06BadJointMoments Reference.MD06JointSupportCounts
open Reference.MD06BadPatternCounts
attribute [local instance] Classical.propDecidable

theorem actual_bad_code_card {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (BadCode S) = 3*S.card + 18*S.card^2 := by
  simp only [BadCode,Fintype.card_sum,Fintype.card_prod,Fintype.card_coe,
    actual_ordered_local_pair_card,Fintype.card_bool]
  ring

theorem actual_supported_bad_card_le {n : ℕ} (S : Finset (Fin n)) :
    Fintype.card (SupportedBadDatum n S) ≤ 3*S.card + 18*S.card^2 := by
  have hdouble (d : DoubleDatum n) :
      VertexSupport (DoublePattern d) = {d.1.val.1,d.1.val.2} := by
    cases hb : d.2.2.2 <;>
      simp only [DoublePattern,hb,Bool.false_eq_true,if_false,if_true,
        actual_two_edge_vertex_support]
  let encode : SupportedBadDatum n S → BadCode S :=
    fun z => match z with
    | ⟨.inl d,hz⟩ => .inl
        (⟨d.1,hz (by simp [BadPattern,actual_loop_vertex_support])⟩,d.2)
    | ⟨.inr d,hz⟩ => .inr
        (⟨d.1.val.1,hz (by simp [BadPattern,hdouble])⟩,
         ⟨d.1.val.2,hz (by simp [BadPattern,hdouble])⟩,
         d.2.1,d.2.2.1,d.2.2.2)
  have hi : Function.Injective encode := by
    rintro ⟨x,hx⟩ ⟨y,hy⟩ h
    apply Subtype.ext
    cases x with
    | inl d =>
      cases y with
      | inl e =>
        simp only [encode,Sum.inl.injEq,Prod.mk.injEq,Subtype.mk.injEq] at h
        exact congrArg Sum.inl (Prod.ext h.1 h.2)
      | inr e => simp only [encode,Sum.inl_ne_inr] at h
    | inr d =>
      cases y with
      | inl e => simp only [encode,Sum.inr_ne_inl] at h
      | inr e =>
        simp only [encode,Sum.inr.injEq,Prod.mk.injEq,Subtype.mk.injEq] at h
        exact congrArg Sum.inr
          (Prod.ext (Subtype.ext (Prod.ext h.1 h.2.1))
            (Prod.ext h.2.2.1 (Prod.ext h.2.2.2.1 h.2.2.2.2)))
  exact (Fintype.card_le_of_injective encode hi).trans (le_of_eq (actual_bad_code_card S))

#print axioms actual_bad_code_card
#print axioms actual_supported_bad_card_le
end Reference.MD06BadSupportEnumeration
