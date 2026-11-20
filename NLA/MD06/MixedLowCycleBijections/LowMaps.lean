module

public import NLA.MD06.MixedLowCycleBijections.LowCounts
public import NLA.MD06.MixedPatternShapes.BadCycleProperties
public import NLA.MD06.BadOverlapExcess.Metadata

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedLowCycleBijections
open Reference.MD06MixedPatternShapes Reference.MD06CanonicalCyclePatterns
open Reference.MD06Simplicity Reference.MD06BadOverlap
attribute [local instance] Classical.propDecidable

theorem actual_loop_canonical_datum_pattern {n : ℕ} (d : LoopDatum n) :
    (LoopCanonicalDatum d).val=LoopPattern d := by
  exact actual_loop_canonical_cycle d

theorem actual_double_canonical_datum_pattern {n : ℕ} (d : DoubleDatum n) :
    (DoubleCanonicalDatum d).val=DoublePattern d := by
  exact actual_double_canonical_cycle d

theorem actual_loop_canonical_datum_injective (n : ℕ) :
    Function.Injective (@LoopCanonicalDatum n) := by
  intro x y h
  apply actual_loop_pattern_injective n
  have hv := congrArg (fun C : CanonicalCycleDatum n 1 => C.val) h
  simpa only [actual_loop_canonical_datum_pattern] using hv

theorem actual_double_canonical_datum_injective (n : ℕ) :
    Function.Injective (@DoubleCanonicalDatum n) := by
  intro x y h
  apply actual_double_pattern_injective n
  have hv := congrArg (fun C : CanonicalCycleDatum n 2 => C.val) h
  simpa only [actual_double_canonical_datum_pattern] using hv

theorem actual_loop_canonical_datum_bijective (n : ℕ) :
    Function.Bijective (@LoopCanonicalDatum n) := by
  have hi := actual_loop_canonical_datum_injective n
  exact ⟨hi,hi.surjective_of_finite (Fintype.equivOfCardEq (actual_loop_canonical_card_equal n))⟩

theorem actual_double_canonical_datum_bijective (n : ℕ) :
    Function.Bijective (@DoubleCanonicalDatum n) := by
  have hi := actual_double_canonical_datum_injective n
  exact ⟨hi,hi.surjective_of_finite (Fintype.equivOfCardEq (actual_double_canonical_card_equal n))⟩

theorem actual_typed_map_bijective (n ell : ℕ) :
    Function.Bijective (@TypedMap n ell) := by
  exact Sum.map_bijective.mpr ⟨Sum.map_bijective.mpr
    ⟨actual_loop_canonical_datum_bijective n,actual_double_canonical_datum_bijective n⟩,
    Function.bijective_id⟩

theorem actual_typed_map_pattern {n ell : ℕ} (d : MarkedDatum n ell) :
    TypedPattern (TypedMap d)=MarkedPattern d := by
  cases d with
  | inl b =>
    cases b with
    | inl L => exact actual_loop_canonical_datum_pattern L
    | inr D => exact actual_double_canonical_datum_pattern D
  | inr C => rfl

#print axioms actual_loop_canonical_datum_pattern
#print axioms actual_double_canonical_datum_pattern
#print axioms actual_loop_canonical_datum_injective
#print axioms actual_double_canonical_datum_injective
#print axioms actual_loop_canonical_datum_bijective
#print axioms actual_double_canonical_datum_bijective
#print axioms actual_typed_map_bijective
#print axioms actual_typed_map_pattern
end Reference.MD06MixedLowCycleBijections
