module

public import NLA.IV04.PaperCanonicalWordBridge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem verified_canonical_word_length (bits : List Bool) :
    (canonicalWord bits).length ≤ bits.length := by
  exact canonical_word_length bits

theorem verified_canonical_word_value (bits : List Bool) :
    wordValue (canonicalWord bits)=wordValue bits := by
  exact canonical_word_value bits

theorem verified_canonical_word_eq_bits (bits : List Bool) :
    canonicalWord bits=(wordValue bits).bits := by
  exact canonical_word_eq_bits bits

theorem verified_canonical_word_idempotent (bits : List Bool) :
    canonicalWord (canonicalWord bits)=canonicalWord bits := by
  exact canonical_word_idempotent bits

theorem verified_canonical_word_cobham :
    Cobham fun v : Fin 1 → List Bool => canonicalWord (v 0) := by
  exact canonical_word_cobham

theorem verified_canonical_word_mem_fp : canonicalWord ∈ FP := by
  exact canonical_word_mem_fp

theorem verified_canonical_word_code_cobham :
    Cobham fun v : Fin 1 → List Bool => canonicalWordCode (v 0) := by
  exact canonical_word_code_cobham

theorem verified_canonical_word_code_mem_fp : canonicalWordCode ∈ FP := by
  exact canonical_word_code_mem_fp

theorem verified_canonical_word_code_length (bits : List Bool) :
    (canonicalWordCode bits).length=2*(wordValue bits).size+1 := by
  exact canonical_word_code_length bits

theorem verified_canonical_word_code_length_bound (bits : List Bool) :
    (canonicalWordCode bits).length ≤ 2*bits.length+1 := by
  exact canonical_word_code_length_bound bits

theorem verified_canonical_word_code_exact (bits : List Bool) :
    canonicalWordCode bits=IV04.Paper.naturalCode (wordValue bits) := by
  exact canonical_word_code_exact bits

theorem verified_natural_encoding_actual_polytime : canonicalWordCode ∈ FP ∧
    ∀ bits, canonicalWordCode bits=IV04.Paper.naturalCode (wordValue bits) := by
  exact natural_encoding_actual_polytime

#print axioms IV04.Paper.Computational.verified_canonical_word_length
#print axioms IV04.Paper.Computational.verified_canonical_word_value
#print axioms IV04.Paper.Computational.verified_canonical_word_eq_bits
#print axioms IV04.Paper.Computational.verified_canonical_word_idempotent
#print axioms IV04.Paper.Computational.verified_canonical_word_cobham
#print axioms IV04.Paper.Computational.verified_canonical_word_mem_fp
#print axioms IV04.Paper.Computational.verified_canonical_word_code_cobham
#print axioms IV04.Paper.Computational.verified_canonical_word_code_mem_fp
#print axioms IV04.Paper.Computational.verified_canonical_word_code_length
#print axioms IV04.Paper.Computational.verified_canonical_word_code_length_bound
#print axioms IV04.Paper.Computational.verified_canonical_word_code_exact
#print axioms IV04.Paper.Computational.verified_natural_encoding_actual_polytime
end IV04.Paper.Computational
