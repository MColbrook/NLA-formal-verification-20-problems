module

public import NLA.IV04.PaperFractionCoefficientProduct
public import NLA.IV04.PaperSignedWordPoly
public import NLA.IV04.PaperCanonicalProduct
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem cleared_fraction_word_cobham :
    Cobham fun v : Fin 3 → List Bool => clearedFractionWord (v 0) (v 1) (v 2) := by
  have hn := Cobham.fstBlockFn (Cobham.proj (1 : Fin 3))
  have hs := Cobham.comp fraction_word_list_denominator_cobham fun _ : Fin 1 =>
    Cobham.proj (2 : Fin 3)
  have hm := Cobham.comp₂ canonical_word_multiply_cobham (Cobham.proj (0 : Fin 3)) hs
  have hp := Cobham.comp (Cobham.bit false) fun _ : Fin 1 => hm
  exact (Cobham.comp₂ polynomial_signed_multiply_cobham hn hp).of_eq fun _ => rfl

theorem cleared_fraction_word_value (prior fraction : List Bool) (payloads : List (List Bool)) :
    signedWordValue (clearedFractionWord prior fraction (payloadListCode payloads))=
      signedWordValue (pairFst fraction)*(wordValue prior : ℤ)*
        (((payloads.map pairSnd).map wordValue).prod : ℤ) := by
  simp only [clearedFractionWord,polynomial_signed_multiply_value,positive_signed_word_value,
    canonical_word_multiply_value,fraction_word_list_denominator_value,Nat.cast_mul,mul_assoc]

theorem cleared_fraction_word_length (prior fraction suffix : List Bool) :
    (clearedFractionWord prior fraction suffix).length ≤ fraction.length+prior.length+8*suffix.length+8 := by
  have hd := fraction_word_list_denominator_length suffix
  have hm := canonical_word_multiply_length prior (fractionWordListDenominator suffix)
  have hn := pairFst_length_le fraction
  have hs := polynomial_signed_multiply_linear_length (pairFst fraction)
    (false :: canonicalWordMultiply prior (fractionWordListDenominator suffix))
  simp only [List.tail_cons,List.length_tail] at hs
  change (polynomialSignedMultiply (pairFst fraction)
    (false :: canonicalWordMultiply prior (fractionWordListDenominator suffix))).length ≤ _
  omega

theorem coefficient_pack_cobham {n : ℕ}
    {rest prior output : (Fin n → List Bool) → List Bool}
    (hr : Cobham rest) (hp : Cobham prior) (ho : Cobham output) :
    Cobham fun v => coefficientPack (rest v) (prior v) (output v) :=
  (Cobham.comp₂ Cobham.pairing hr (Cobham.comp₂ Cobham.pairing hp ho)).of_eq fun _ => rfl

theorem fraction_coefficient_step_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionCoefficientStep (v 0) := by
  have hr : Cobham fun v : Fin 1 → List Bool => coefficientRest (v 0) := Cobham.fstBlockFn (.proj 0)
  have hp : Cobham fun v : Fin 1 → List Bool => coefficientPrefix (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0))
  have ho : Cobham fun v : Fin 1 → List Bool => coefficientOutput (v 0) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0))
  have hfield := Cobham.fstBlockFn hr
  have hsuffix := Cobham.sndBlockFn hr
  have hnext := Cobham.comp₂ canonical_word_multiply_cobham hp (Cobham.sndBlockFn hfield)
  let args : Fin 3 → (Fin 1 → List Bool) → List Bool :=
    ![fun v => coefficientPrefix (v 0),fun v => pairFst (coefficientRest (v 0)),
      fun v => pairSnd (coefficientRest (v 0))]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i
    · simpa [args] using hp
    · simpa [args] using hfield
    · simpa [args] using hsuffix
  have hword := Cobham.comp cleared_fraction_word_cobham ha
  have hout := Cobham.comp₂ Cobham.pairing hword ho
  exact (Cobham.iteFn (Cobham.nonemptyFn hr)
    (coefficient_pack_cobham hsuffix hnext hout) (Cobham.proj 0)).of_eq fun _ => rfl

theorem fraction_coefficient_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => fractionCoefficientInitial (v 0) :=
  (coefficient_pack_cobham (Cobham.proj (0 : Fin 1)) (Cobham.const [true]) (Cobham.const [])).of_eq fun _ => rfl

#print axioms fraction_coefficient_step_cobham
end IV04.Paper.Computational
