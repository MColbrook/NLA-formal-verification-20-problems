module

public import NLA.IV04.PaperCanonicalWord
public import NLA.IV04.PaperEncodingDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem canonical_word_code_exact (bits : List Bool) :
    canonicalWordCode bits=IV04.Paper.naturalCode (wordValue bits) := by
  simp [canonicalWordCode,canonical_word_eq_bits,IV04.Paper.naturalCode]

theorem natural_encoding_actual_polytime : canonicalWordCode ∈ FP ∧
    ∀ bits, canonicalWordCode bits=IV04.Paper.naturalCode (wordValue bits) :=
  ⟨canonical_word_code_mem_fp,canonical_word_code_exact⟩

#print axioms natural_encoding_actual_polytime
end IV04.Paper.Computational
