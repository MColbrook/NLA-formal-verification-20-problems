module

public import NLA.IV04.PaperNaturalParserPoly
public import NLA.IV04.PaperCanonicalWordBridge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem read_unary_stages (input : List Bool) :
    IV04.Paper.readUnary input=
      if input.drop (headerWord input).length=[] then none
      else some ((headerWord input).length,naturalParseRest input) := by
  induction input with
  | nil => rfl
  | cons b bits ih =>
    cases b
    · rfl
    · simp only [IV04.Paper.readUnary,headerWord,List.length_cons,
        List.drop_succ_cons,naturalParseRest] at ih ⊢
      rw [ih]
      split_ifs <;> rfl

theorem natural_parse_flag_stages (input : List Bool) :
    naturalParseFlag input=
      if input.drop (headerWord input).length=[] then [false]
      else if (headerWord input).length ≤ (naturalParseRest input).length then [true] else [false] := by
  unfold naturalParseFlag
  cases hrest : input.drop (headerWord input).length with
  | nil => simp [nonemptyFlag,andBit,caseBit₀,caseBit]
  | cons b bits =>
    simp only [List.cons_ne_nil,ite_false,nonemptyFlag_cons,andBit,caseBit₀_cons,Bool.cond_true]
    cases hdrop : (headerWord input).drop (naturalParseRest input).length with
    | nil =>
      have hl := congrArg List.length hdrop
      simp only [List.length_drop,List.length_nil] at hl
      have hb : (headerWord input).length ≤ (naturalParseRest input).length := by omega
      simp [hb,nonemptyFlag,notBit,caseBit₀,caseBit]
    | cons c tail =>
      have hl := congrArg List.length hdrop
      simp only [List.length_drop,List.length_cons] at hl
      have hb : ¬ (headerWord input).length ≤ (naturalParseRest input).length := by omega
      simp [hb,nonemptyFlag,notBit,caseBit₀,caseBit]

theorem read_natural_stages (input : List Bool) :
    IV04.Paper.readNatural input=
      if input.drop (headerWord input).length=[] then none
      else if (headerWord input).length ≤ (naturalParseRest input).length
      then some (wordValue ((naturalParseRest input).take (headerWord input).length),
        (naturalParseRest input).drop (headerWord input).length)
      else none := by
  unfold IV04.Paper.readNatural
  rw [read_unary_stages]
  split_ifs <;> simp_all [word_value_foldr]

theorem natural_parser_flag (input : List Bool) :
    Complexity.pairFst (encodedNaturalParser input)=naturalParseFlag input := by
  simp [encodedNaturalParser]

theorem natural_parser_payload (input : List Bool) :
    Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))=
      (naturalParseRest input).take (headerWord input).length := by
  simp [encodedNaturalParser]

theorem natural_parser_tail (input : List Bool) :
    Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))=
      (naturalParseRest input).drop (headerWord input).length := by
  simp [encodedNaturalParser]

theorem natural_parser_exact (input : List Bool) :
    (if Complexity.pairFst (encodedNaturalParser input)=[true] then
      some (wordValue (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input)))
      else none)=IV04.Paper.readNatural input := by
  rw [natural_parser_flag,natural_parser_payload,natural_parser_tail,
    natural_parse_flag_stages,read_natural_stages]
  split_ifs <;> simp_all

theorem natural_parser_actual_polytime : encodedNaturalParser ∈ FP ∧
    ∀ input,
    (if Complexity.pairFst (encodedNaturalParser input)=[true] then
      some (wordValue (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input)))
      else none)=IV04.Paper.readNatural input :=
  ⟨encoded_natural_parser_mem_fp,natural_parser_exact⟩

#print axioms natural_parser_actual_polytime
end IV04.Paper.Computational
