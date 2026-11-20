module

public import NLA.IV04.PaperFractionWordSemantics
public import NLA.IV04.PaperSignedWordPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem normalize_fraction_word_cobham :
    Cobham fun v : Fin 1 → List Bool => normalizeFractionWord (v 0) := by
  have hn := Cobham.comp canonical_word_cobham fun _ : Fin 1 =>
    Cobham.sndBlockFn (Cobham.proj (0 : Fin 1))
  have hp := Cobham.comp₂ Cobham.pairing (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) hn
  exact (Cobham.iteFn (Cobham.nonemptyFn hn) hp (Cobham.const (pair [false] [true]))).of_eq fun _ => rfl

theorem normalize_fraction_word_mem_fp : normalizeFractionWord ∈ FP :=
  CobhamFP_subset_FP normalize_fraction_word_cobham

theorem polynomial_fraction_add_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialFractionAdd (v 0) (v 1) := by
  have hl : Cobham fun v : Fin 2 → List Bool => normalizeFractionWord (v 0) :=
    (Cobham.comp normalize_fraction_word_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham fun v : Fin 2 → List Bool => normalizeFractionWord (v 1) :=
    (Cobham.comp normalize_fraction_word_cobham fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hln := Cobham.fstBlockFn hl
  have hrn := Cobham.fstBlockFn hr
  have hld := Cobham.sndBlockFn hl
  have hrd := Cobham.sndBlockFn hr
  have hpl : Cobham fun v => false :: pairSnd (normalizeFractionWord (v 0)) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => hld).of_eq fun _ => rfl
  have hpr : Cobham fun v => false :: pairSnd (normalizeFractionWord (v 1)) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => hrd).of_eq fun _ => rfl
  have hn := Cobham.comp₂ polynomial_signed_add_cobham
    (Cobham.comp₂ polynomial_signed_multiply_cobham hln hpr)
    (Cobham.comp₂ polynomial_signed_multiply_cobham hrn hpl)
  have hd := Cobham.comp₂ polynomial_word_multiply_cobham hld hrd
  exact (Cobham.comp₂ Cobham.pairing hn hd).of_eq fun _ => rfl

theorem polynomial_fraction_multiply_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialFractionMultiply (v 0) (v 1) := by
  have hl : Cobham fun v : Fin 2 → List Bool => normalizeFractionWord (v 0) :=
    (Cobham.comp normalize_fraction_word_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hr : Cobham fun v : Fin 2 → List Bool => normalizeFractionWord (v 1) :=
    (Cobham.comp normalize_fraction_word_cobham fun _ : Fin 1 => .proj 1).of_eq fun _ => rfl
  have hn := Cobham.comp₂ polynomial_signed_multiply_cobham (Cobham.fstBlockFn hl) (Cobham.fstBlockFn hr)
  have hd := Cobham.comp₂ polynomial_word_multiply_cobham (Cobham.sndBlockFn hl) (Cobham.sndBlockFn hr)
  exact (Cobham.comp₂ Cobham.pairing hn hd).of_eq fun _ => rfl

theorem encoded_fraction_add_mem_fp : encodedPolynomialFractionAdd ∈ FP := by
  have h := Cobham.comp₂ polynomial_fraction_add_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun v => by simp [encodedPolynomialFractionAdd])

theorem encoded_fraction_multiply_mem_fp : encodedPolynomialFractionMultiply ∈ FP := by
  have h := Cobham.comp₂ polynomial_fraction_multiply_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun v => by simp [encodedPolynomialFractionMultiply])

theorem normalize_fraction_actual_polytime : normalizeFractionWord ∈ FP ∧
    ∀ input, fractionWordValue (normalizeFractionWord input)=fractionWordValue input ∧
      0 < wordValue (pairSnd (normalizeFractionWord input)) :=
  ⟨normalize_fraction_word_mem_fp,fun input =>
    ⟨normalize_fraction_word_value input,normalize_fraction_denominator_positive input⟩⟩

theorem encoded_fraction_add_actual_polytime : encodedPolynomialFractionAdd ∈ FP ∧
    ∀ left right, fractionWordValue (encodedPolynomialFractionAdd (pair left right))=
      fractionWordValue left+fractionWordValue right := by
  refine ⟨encoded_fraction_add_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialFractionAdd] using polynomial_fraction_add_value left right

theorem encoded_fraction_multiply_actual_polytime : encodedPolynomialFractionMultiply ∈ FP ∧
    ∀ left right, fractionWordValue (encodedPolynomialFractionMultiply (pair left right))=
      fractionWordValue left*fractionWordValue right := by
  refine ⟨encoded_fraction_multiply_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialFractionMultiply] using polynomial_fraction_multiply_value left right

#print axioms encoded_fraction_add_actual_polytime
end IV04.Paper.Computational
