module

public import NLA.IV04.PaperTridiagonalCellDefinitions
public import NLA.IV04.PaperSignedOrderPoly
public import NLA.IV04.PaperWordAdderPoly
public import NLA.IV04.PaperWordAdderSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem and_decide_flags (p q : Prop) [Decidable p] [Decidable q] :
    andBit [decide p] [decide q]=[decide (p ∧ q)] := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq,andBit,caseBit₀]

theorem signed_zero_flag_value (word : List Bool) :
    signedZeroFlag word=[decide (signedWordValue word=0)] := by
  have h0 : signedWordValue [false]=0 := rfl
  rw [signedZeroFlag,polynomial_signed_le_value,polynomial_signed_le_value,h0,and_decide_flags]
  have h : (signedWordValue word ≤ 0 ∧ 0 ≤ signedWordValue word) ↔ signedWordValue word=0 := by omega
  simp only [h]

theorem tridiagonal_band_flag_value (row column : List Bool) :
    tridiagonalBandFlag row column=
      [decide (wordValue row ≤ wordValue column+1 ∧ wordValue column ≤ wordValue row+1)] := by
  rw [tridiagonalBandFlag,polynomial_word_le_value,polynomial_word_le_value,
    polynomial_word_add_value,polynomial_word_add_value]
  have h1 : wordValue [true]=1 := rfl
  rw [h1,and_decide_flags]

theorem tridiagonal_endpoint_flag_value (row column lower upper : List Bool) :
    tridiagonalEndpointFlag row column lower upper=
      [decide ((wordValue row ≤ wordValue column+1 ∧ wordValue column ≤ wordValue row+1) ∨
        (signedWordValue lower=0 ∧ signedWordValue upper=0))] := by
  rw [tridiagonalEndpointFlag,tridiagonal_band_flag_value,
    signed_zero_flag_value,signed_zero_flag_value,and_decide_flags]
  by_cases hb : wordValue row ≤ wordValue column+1 ∧ wordValue column ≤ wordValue row+1 <;>
    simp [hb,caseBit₀]

theorem signed_zero_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => signedZeroFlag (v 0) :=
  (Cobham.andFn (Cobham.comp₂ polynomial_signed_le_cobham (.proj 0) (.const [false]))
    (Cobham.comp₂ polynomial_signed_le_cobham (.const [false]) (.proj 0))).of_eq fun _ => rfl

theorem tridiagonal_band_flag_cobham :
    Cobham fun v : Fin 2 → List Bool => tridiagonalBandFlag (v 0) (v 1) :=
  (Cobham.andFn (Cobham.comp₂ polynomial_word_le_cobham (.proj 0)
    (Cobham.comp₂ polynomial_word_add_cobham (.proj 1) (.const [true])))
    (Cobham.comp₂ polynomial_word_le_cobham (.proj 1)
      (Cobham.comp₂ polynomial_word_add_cobham (.proj 0) (.const [true])))).of_eq fun _ => rfl

theorem tridiagonal_endpoint_flag_cobham :
    Cobham fun v : Fin 4 → List Bool => tridiagonalEndpointFlag (v 0) (v 1) (v 2) (v 3) :=
  (Cobham.iteFn (Cobham.comp₂ tridiagonal_band_flag_cobham (.proj 0) (.proj 1)) (.const [true])
    (Cobham.andFn (Cobham.comp signed_zero_flag_cobham fun _ : Fin 1 => .proj 2)
      (Cobham.comp signed_zero_flag_cobham fun _ : Fin 1 => .proj 3))).of_eq fun _ => rfl

theorem encoded_tridiagonal_endpoint_flag_cobham :
    Cobham fun v : Fin 1 → List Bool => encodedTridiagonalEndpointFlag (v 0) := by
  let args : Fin 4 → (Fin 1 → List Bool) → List Bool := ![
    fun v => pairFst (v 0),fun v => pairFst (pairSnd (v 0)),
    fun v => pairFst (pairSnd (pairSnd (v 0))),fun v => pairSnd (pairSnd (pairSnd (v 0)))]
  have ha : ∀ i, Cobham (args i) := by
    intro i;fin_cases i
    · exact Cobham.fstBlockFn (.proj 0)
    · exact Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0))
    · exact Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0)))
    · exact Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0)))
  exact (Cobham.comp tridiagonal_endpoint_flag_cobham ha).of_eq fun _ => rfl

theorem encoded_tridiagonal_endpoint_flag_mem_fp : encodedTridiagonalEndpointFlag ∈ FP :=
  CobhamFP_subset_FP encoded_tridiagonal_endpoint_flag_cobham

theorem encoded_tridiagonal_endpoint_flag_value (row column lower upper : List Bool) :
    encodedTridiagonalEndpointFlag (pair row (pair column (pair lower upper)))=
      [decide ((wordValue row ≤ wordValue column+1 ∧ wordValue column ≤ wordValue row+1) ∨
        (signedWordValue lower=0 ∧ signedWordValue upper=0))] := by
  simpa only [encodedTridiagonalEndpointFlag,pairFst_pair,pairSnd_pair] using
    tridiagonal_endpoint_flag_value row column lower upper

theorem tridiagonal_endpoint_offband (row column lower upper : List Bool)
    (hoff : ¬ (wordValue row ≤ wordValue column+1 ∧ wordValue column ≤ wordValue row+1)) :
    encodedTridiagonalEndpointFlag (pair row (pair column (pair lower upper)))=[true] ↔
      signedWordValue lower=0 ∧ signedWordValue upper=0 := by
  rw [encoded_tridiagonal_endpoint_flag_value]
  simp [hoff]

#print axioms encoded_tridiagonal_endpoint_flag_mem_fp
#print axioms tridiagonal_endpoint_offband
end IV04.Paper.Computational
