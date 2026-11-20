module

public import NLA.MD06.CombinedDescendingMoments.Definitions
public import NLA.MD06.MixedLowCycleBijections.MarkedBinding

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06CombinedMoments
open Reference.MD06MixedPatternShapes Reference.MD06MixedLowCycleBijections
attribute [local instance] Classical.propDecidable

theorem actual_typed_tagged_pattern {n ell : ℕ} (d : TypedDatum n ell) :
    TaggedPattern (typedTaggedEquiv n ell d)=TypedPattern d := by
  cases d with
  | inl b => cases b <;> rfl
  | inr C => rfl

theorem actual_marked_to_tagged_bijective (n ell : ℕ) :
    Function.Bijective (@MarkedToTagged n ell) := by
  exact (typedTaggedEquiv n ell).bijective.comp (actual_typed_map_bijective n ell)

theorem actual_marked_to_tagged_pattern {n ell : ℕ} (d : MarkedDatum n ell) :
    TaggedPattern (MarkedToTagged d)=MarkedPattern d := by
  exact (actual_typed_tagged_pattern (TypedMap d)).trans (actual_typed_map_pattern d)

theorem actual_tag_length_positive (ell : ℕ) (hell : 0<ell) (t : MarkTag) :
    0<TagLength ell t := by
  cases t <;> simp [TagLength,hell]

#print axioms actual_typed_tagged_pattern
#print axioms actual_marked_to_tagged_bijective
#print axioms actual_marked_to_tagged_pattern
#print axioms actual_tag_length_positive
end Reference.MD06CombinedMoments
