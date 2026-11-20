module

public import NLA.IV04.PaperFractionOutputPoly
public import NLA.IV04.PaperCanonicalWordBridge
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
theorem polynomial_fraction_output_shape (input : List Bool) :
    polynomialFractionOutput input = firstBit (pairFst input) ::
      (IV04.Paper.naturalCode (wordValue (pairFst input).tail) ++
        IV04.Paper.naturalCode (wordValue (pairSnd input))) := by
  simp only [polynomialFractionOutput,head_flag,canonical_word_code_exact]
  generalize firstBit (pairFst input) = b
  cases b <;> rfl
theorem polynomial_fraction_output_read (input tail : List Bool) :
    IV04.Paper.readRational (polynomialFractionOutput input ++ tail) =
      some (fractionWordValue input,tail) := by
  rw [polynomial_fraction_output_shape]
  simp only [List.cons_append,List.append_assoc,IV04.Paper.readRational,
    IV04.Paper.read_natural_code,bind,Option.bind_some]
  simp [fractionWordValue,signedWordValue]
theorem fraction_output_actual_polytime : polynomialFractionOutput ∈ FP ∧
    ∀ input tail, IV04.Paper.readRational (polynomialFractionOutput input ++ tail) =
      some (fractionWordValue input,tail) :=
  ⟨polynomial_fraction_output_mem_fp,polynomial_fraction_output_read⟩
#print axioms fraction_output_actual_polytime
end IV04.Paper.Computational
