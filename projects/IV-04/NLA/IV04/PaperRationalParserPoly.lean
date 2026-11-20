module

public import NLA.IV04.PaperRationalParserSemantics
public import NLA.IV04.PaperNaturalParserPoly
public import NLA.IV04.PaperFractionWordPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem rational_parser_first_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalParserFirst (v 0) :=
  (Cobham.comp encoded_natural_parser_cobham fun _ : Fin 1 => Cobham.tailFn (.proj 0)).of_eq fun _ => rfl

theorem rational_parser_second_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalParserSecond (v 0) :=
  (Cobham.comp encoded_natural_parser_cobham fun _ : Fin 1 =>
    Cobham.sndBlockFn (Cobham.sndBlockFn rational_parser_first_cobham)).of_eq fun _ => rfl

theorem rational_parser_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalParserFlag (v 0) :=
  (Cobham.andFn (Cobham.nonemptyFn (Cobham.proj (0 : Fin 1)))
    (Cobham.andFn (Cobham.fstBlockFn rational_parser_first_cobham)
      (Cobham.fstBlockFn rational_parser_second_cobham))).of_eq fun _ => rfl

theorem rational_parser_fraction_cobham :
    Cobham fun v : Fin 1 → List Bool => rationalParserFraction (v 0) := by
  have hn := signed_word_pack_cobham (Cobham.headFlagFn (Cobham.proj (0 : Fin 1)))
    (Cobham.fstBlockFn (Cobham.sndBlockFn rational_parser_first_cobham))
  have hd := Cobham.fstBlockFn (Cobham.sndBlockFn rational_parser_second_cobham)
  have hp := Cobham.comp₂ Cobham.pairing hn hd
  exact (Cobham.comp normalize_fraction_word_cobham fun _ : Fin 1 => hp).of_eq fun v => by
    unfold rationalParserFraction
    apply congrArg normalizeFractionWord
    apply congrArg₂ Complexity.pair
    · apply congrArg₂ signedWordPack <;> rfl
    · rfl

set_option maxHeartbeats 2000000 in
theorem encoded_rational_parser_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedRationalParser (v 0) := by
  have ht := Cobham.sndBlockFn (Cobham.sndBlockFn rational_parser_second_cobham)
  exact (Cobham.comp₂ Cobham.pairing rational_parser_flag_cobham
    (Cobham.comp₂ Cobham.pairing rational_parser_fraction_cobham ht)).of_eq fun v => by
      unfold encodedRationalParser
      apply congrArg₂ Complexity.pair
      · rfl
      · apply congrArg₂ Complexity.pair <;> rfl

theorem encoded_rational_parser_mem_fp : encodedRationalParser ∈ FP :=
  CobhamFP_subset_FP encoded_rational_parser_cobham

theorem rational_parser_actual_polytime : encodedRationalParser ∈ FP ∧
    ∀ input,
    (if pairFst (encodedRationalParser input)=[true] then
      some (fractionWordValue (pairFst (pairSnd (encodedRationalParser input))),
        pairSnd (pairSnd (encodedRationalParser input)))
      else none)=IV04.Paper.readRational input :=
  ⟨encoded_rational_parser_mem_fp,rational_parser_exact⟩

#print axioms rational_parser_actual_polytime
end IV04.Paper.Computational
