module

public import NLA.IV04.PaperSignedWordSemantics
public import NLA.IV04.PaperWordSubtractionPoly
public import NLA.IV04.PaperWordMultiplierPoly
public import NLA.IV04.PaperCanonicalWord
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem signed_word_pack_cobham {n : ℕ}
    {flag magnitude : (Fin n → List Bool) → List Bool}
    (hf : Cobham flag) (hm : Cobham magnitude) :
    Cobham fun v => signedWordPack (flag v) (magnitude v) := by
  have hn := Cobham.comp canonical_word_cobham fun _ : Fin 1 => hm
  have ht : Cobham fun v => true :: canonicalWord (magnitude v) :=
    (Cobham.comp (.bit true) fun _ : Fin 1 => hn).of_eq fun _ => rfl
  have hz : Cobham fun v => false :: canonicalWord (magnitude v) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => hn).of_eq fun _ => rfl
  exact (Cobham.iteFn hf ht hz).of_eq fun _ => rfl

theorem polynomial_signed_neg_cobham :
    Cobham fun v : Fin 1 → List Bool => polynomialSignedNeg (v 0) :=
  (signed_word_pack_cobham (Cobham.notFn (Cobham.headFlagFn (.proj 0)))
    (Cobham.tailFn (.proj 0))).of_eq fun _ => rfl

theorem polynomial_signed_add_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialSignedAdd (v 0) (v 1) := by
  have ha := Cobham.headFlagFn (Cobham.proj (0 : Fin 2))
  have hb := Cobham.headFlagFn (Cobham.proj (1 : Fin 2))
  have hx := Cobham.tailFn (Cobham.proj (0 : Fin 2))
  have hy := Cobham.tailFn (Cobham.proj (1 : Fin 2))
  have hc := Cobham.comp₂ polynomial_word_le_cobham hx hy
  have hsubr := signed_word_pack_cobham hb (Cobham.comp₂ polynomial_word_sub_cobham hy hx)
  have hsubl := signed_word_pack_cobham ha (Cobham.comp₂ polynomial_word_sub_cobham hx hy)
  have hadd := signed_word_pack_cobham ha (Cobham.comp₂ polynomial_word_add_cobham hx hy)
  exact (Cobham.iteFn (xor_flag_cobham ha hb) (Cobham.iteFn hc hsubr hsubl) hadd).of_eq fun _ => rfl

theorem polynomial_signed_multiply_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialSignedMultiply (v 0) (v 1) := by
  have hs := xor_flag_cobham (Cobham.headFlagFn (Cobham.proj (0 : Fin 2)))
    (Cobham.headFlagFn (Cobham.proj (1 : Fin 2)))
  have hm := Cobham.comp₂ polynomial_word_multiply_cobham
    (Cobham.tailFn (Cobham.proj (0 : Fin 2))) (Cobham.tailFn (Cobham.proj (1 : Fin 2)))
  exact (signed_word_pack_cobham hs hm).of_eq fun _ => rfl

theorem signed_neg_mem_fp : polynomialSignedNeg ∈ FP :=
  CobhamFP_subset_FP polynomial_signed_neg_cobham

theorem encoded_signed_add_mem_fp : encodedPolynomialSignedAdd ∈ FP := by
  have h := Cobham.comp₂ polynomial_signed_add_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun v => by simp [encodedPolynomialSignedAdd])

theorem encoded_signed_multiply_mem_fp : encodedPolynomialSignedMultiply ∈ FP := by
  have h := Cobham.comp₂ polynomial_signed_multiply_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun v => by simp [encodedPolynomialSignedMultiply])

theorem signed_neg_actual_polytime : polynomialSignedNeg ∈ FP ∧
    ∀ bits, signedWordValue (polynomialSignedNeg bits)=-signedWordValue bits :=
  ⟨signed_neg_mem_fp,polynomial_signed_neg_value⟩

theorem encoded_signed_add_actual_polytime : encodedPolynomialSignedAdd ∈ FP ∧
    ∀ left right, signedWordValue (encodedPolynomialSignedAdd (Complexity.pair left right))=
      signedWordValue left+signedWordValue right := by
  refine ⟨encoded_signed_add_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialSignedAdd] using polynomial_signed_add_value left right

theorem encoded_signed_multiply_actual_polytime : encodedPolynomialSignedMultiply ∈ FP ∧
    ∀ left right, signedWordValue (encodedPolynomialSignedMultiply (Complexity.pair left right))=
      signedWordValue left*signedWordValue right := by
  refine ⟨encoded_signed_multiply_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialSignedMultiply] using polynomial_signed_multiply_value left right

#print axioms encoded_signed_add_actual_polytime
end IV04.Paper.Computational
