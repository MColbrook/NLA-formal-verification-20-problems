module

public import NLA.IV04.PaperCanonicalProductDefinitions
public import NLA.IV04.PaperCanonicalWord
public import NLA.IV04.PaperWordMultiplierPoly
public import NLA.IV04.PaperSignedWordBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem canonical_word_multiply_value (left right : List Bool) :
    wordValue (canonicalWordMultiply left right)=wordValue left*wordValue right := by
  simp [canonicalWordMultiply,canonical_word_value,polynomial_word_multiply_value]

theorem binary_product_size (left right : List Bool) :
    (wordValue left*wordValue right).size ≤ left.length+right.length := by
  apply Nat.size_le.mpr
  have hl := word_value_lt_pow_length left
  have hr := word_value_lt_pow_length right
  rw [pow_add]
  have hp := Nat.mul_le_mul
    (show wordValue left+1 ≤ (2 : ℕ)^left.length by omega)
    (show wordValue right+1 ≤ (2 : ℕ)^right.length by omega)
  nlinarith

theorem canonical_word_multiply_length (left right : List Bool) :
    (canonicalWordMultiply left right).length ≤ left.length+right.length := by
  simpa only [canonicalWordMultiply,canonical_word_eq_bits,polynomial_word_multiply_value,
    Nat.size_eq_bits_len] using binary_product_size left right

theorem polynomial_signed_multiply_linear_length (left right : List Bool) :
    (polynomialSignedMultiply left right).length ≤ left.tail.length+right.tail.length+1 := by
  have hs := signed_word_pack_length
    (xorFlag (bitAt [] left) (bitAt [] right)) (canonicalWordMultiply left.tail right.tail)
  have he : polynomialSignedMultiply left right=
      signedWordPack (xorFlag (bitAt [] left) (bitAt [] right))
        (canonicalWordMultiply left.tail right.tail) := by
    simp only [polynomialSignedMultiply,canonicalWordMultiply,signedWordPack,canonical_word_idempotent]
  rw [he]
  have hp := canonical_word_multiply_length left.tail right.tail
  omega

theorem canonical_word_multiply_cobham :
    Cobham fun v : Fin 2 → List Bool => canonicalWordMultiply (v 0) (v 1) :=
  (Cobham.comp canonical_word_cobham fun _ : Fin 1 => polynomial_word_multiply_cobham).of_eq fun _ => rfl

theorem encoded_canonical_word_multiply_mem_fp : encodedCanonicalWordMultiply ∈ FP := by
  have h := Cobham.comp₂ canonical_word_multiply_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun _ => rfl)

theorem canonical_word_multiply_actual_polytime : encodedCanonicalWordMultiply ∈ FP ∧
    ∀ left right, wordValue (encodedCanonicalWordMultiply (pair left right))=wordValue left*wordValue right ∧
      (encodedCanonicalWordMultiply (pair left right)).length ≤ left.length+right.length := by
  refine ⟨encoded_canonical_word_multiply_mem_fp,?_⟩
  intro left right
  simpa only [encodedCanonicalWordMultiply,pairFst_pair,pairSnd_pair] using
    And.intro (canonical_word_multiply_value left right) (canonical_word_multiply_length left right)

#print axioms canonical_word_multiply_actual_polytime
end IV04.Paper.Computational
