module

public import NLA.MD06.MixedLowCycleBijections.Definitions
public import NLA.MD06.SupportedCanonicalCycles.Cardinality
public import NLA.MD06.BadPatternCounts.Cardinality

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06MixedLowCycleBijections
open Reference.MD06SupportedCanonicalCycles Reference.MD06CanonicalCyclePatterns
open Reference.MD06Simplicity Reference.MD06BadPatternCounts
attribute [local instance] Classical.propDecidable

theorem actual_global_canonical_cycle_scaled_card (n ell : ℕ) [NeZero ell] :
    (2*ell)*Fintype.card (CanonicalCycleDatum n ell)=n.descFactorial ell*6^ell := by
  let e : CanonicalCycleDatum n ell ≃ SupportedCanonicalCycle (Finset.univ : Finset (Fin n)) ell :=
    { toFun := fun C => ⟨C,Finset.subset_univ _⟩
      invFun := fun C => C.val
      left_inv := fun C => rfl
      right_inv := by intro C;rfl }
  have hc := actual_supported_canonical_cycle_card (Finset.univ : Finset (Fin n)) (ell:=ell)
  rw [←Fintype.card_congr e,Finset.card_univ,Fintype.card_fin] at hc
  exact hc

theorem actual_loop_canonical_card_equal (n : ℕ) :
    Fintype.card (LoopDatum n)=Fintype.card (CanonicalCycleDatum n 1) := by
  have hc := actual_global_canonical_cycle_scaled_card n 1
  simp only [Nat.descFactorial_one,pow_one] at hc
  rw [actual_loop_datum_card]
  omega

theorem actual_double_canonical_card_equal (n : ℕ) :
    Fintype.card (DoubleDatum n)=Fintype.card (CanonicalCycleDatum n 2) := by
  have hc := actual_global_canonical_cycle_scaled_card n 2
  rw [Nat.descFactorial_eq_factorial_mul_choose] at hc
  norm_num at hc
  rw [actual_double_datum_card]
  omega

#print axioms actual_global_canonical_cycle_scaled_card
#print axioms actual_loop_canonical_card_equal
#print axioms actual_double_canonical_card_equal
end Reference.MD06MixedLowCycleBijections
