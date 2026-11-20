module

public import NLA.IV04.PaperSignedOrderSemantics
public import NLA.IV04.PaperFractionWordPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem signed_negative_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => signedNegativeFlag (v 0) := by
  have hm := Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.tailFn (Cobham.proj (0 : Fin 1))
  exact (Cobham.iteFn (Cobham.andFn (Cobham.headFlagFn (.proj 0)) (Cobham.nonemptyFn hm))
    (Cobham.const [true]) (Cobham.const [false])).of_eq fun _ => rfl

theorem polynomial_signed_le_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialSignedLe (v 0) (v 1) := by
  have ha : Cobham fun v : Fin 2 → List Bool => signedNegativeFlag (v 0) :=
    (Cobham.comp signed_negative_flag_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hb : Cobham fun v : Fin 2 → List Bool => signedNegativeFlag (v 1) :=
    (Cobham.comp signed_negative_flag_cobham fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hx := Cobham.tailFn (Cobham.proj (0 : Fin 2))
  have hy := Cobham.tailFn (Cobham.proj (1 : Fin 2))
  have hf := Cobham.comp₂ polynomial_word_le_cobham hx hy
  have hr := Cobham.comp₂ polynomial_word_le_cobham hy hx
  exact (Cobham.iteFn (xor_flag_cobham ha hb) ha (Cobham.iteFn ha hr hf)).of_eq fun _ => rfl

theorem polynomial_fraction_le_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialFractionLe (v 0) (v 1) := by
  have hl : Cobham fun v : Fin 2 → List Bool => normalizeFractionWord (v 0) :=
    (Cobham.comp normalize_fraction_word_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham fun v : Fin 2 → List Bool => normalizeFractionWord (v 1) :=
    (Cobham.comp normalize_fraction_word_cobham fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hpl : Cobham fun v => false :: pairSnd (normalizeFractionWord (v 0)) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => Cobham.sndBlockFn hl).of_eq fun _ => rfl
  have hpr : Cobham fun v => false :: pairSnd (normalizeFractionWord (v 1)) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => Cobham.sndBlockFn hr).of_eq fun _ => rfl
  exact (Cobham.comp₂ polynomial_signed_le_cobham
    (Cobham.comp₂ polynomial_signed_multiply_cobham (Cobham.fstBlockFn hl) hpr)
    (Cobham.comp₂ polynomial_signed_multiply_cobham (Cobham.fstBlockFn hr) hpl)).of_eq fun _ => rfl

theorem encoded_signed_le_mem_fp : encodedPolynomialSignedLe ∈ FP := by
  have h := Cobham.comp₂ polynomial_signed_le_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun _ => rfl)

theorem encoded_fraction_le_mem_fp : encodedPolynomialFractionLe ∈ FP := by
  have h := Cobham.comp₂ polynomial_fraction_le_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun _ => rfl)

theorem encoded_signed_le_actual_polytime : encodedPolynomialSignedLe ∈ FP ∧
    ∀ left right, encodedPolynomialSignedLe (pair left right)=
      [decide (signedWordValue left ≤ signedWordValue right)] := by
  refine ⟨encoded_signed_le_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialSignedLe] using polynomial_signed_le_value left right

theorem encoded_fraction_le_actual_polytime : encodedPolynomialFractionLe ∈ FP ∧
    ∀ left right, encodedPolynomialFractionLe (pair left right)=
      [decide (fractionWordValue left ≤ fractionWordValue right)] := by
  refine ⟨encoded_fraction_le_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialFractionLe] using polynomial_fraction_le_value left right

#print axioms encoded_fraction_le_actual_polytime
end IV04.Paper.Computational
