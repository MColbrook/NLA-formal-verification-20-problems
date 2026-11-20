module

public import NLA.IV04.PaperIntegerContinuantMachineDefinitions
public import NLA.IV04.PaperSignedWordSharpBounds
public import NLA.IV04.PaperWordListProductBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem integer_continuant_next_value (row previous before : List Bool) :
    signedWordValue (integerContinuantNext row previous before)=
      signedWordValue (pairFst row)*signedWordValue previous-
        signedWordValue (pairFst (pairSnd row))*signedWordValue (pairSnd (pairSnd row))*signedWordValue before := by
  simp only [integerContinuantNext,polynomial_signed_add_value,polynomial_signed_multiply_value,
    polynomial_signed_neg_value,sub_eq_add_neg]

theorem integer_continuant_next_row_value (diagonal lower upper previous before : List Bool) :
    signedWordValue (integerContinuantNext (integerContinuantRow diagonal lower upper) previous before)=
      signedWordValue diagonal*signedWordValue previous-
        signedWordValue lower*signedWordValue upper*signedWordValue before := by
  simp only [integer_continuant_next_value,integerContinuantRow,pairFst_pair,pairSnd_pair]

theorem integer_continuant_next_length (row previous before : List Bool) :
    (integerContinuantNext row previous before).length ≤ max previous.length before.length+row.length+4 := by
  have hb := pair_projection_budget row
  have hb' := pair_projection_budget (pairSnd row)
  have hx := polynomial_signed_multiply_linear_length (pairFst row) previous
  have hc := polynomial_signed_multiply_linear_length (pairFst (pairSnd row)) (pairSnd (pairSnd row))
  have hy := polynomial_signed_multiply_linear_length
    (polynomialSignedMultiply (pairFst (pairSnd row)) (pairSnd (pairSnd row))) before
  have hn := polynomial_signed_neg_tail_length
    (polynomialSignedMultiply (polynomialSignedMultiply (pairFst (pairSnd row)) (pairSnd (pairSnd row))) before)
  have hs := polynomial_signed_add_max_length (polynomialSignedMultiply (pairFst row) previous)
    (polynomialSignedNeg
      (polynomialSignedMultiply (polynomialSignedMultiply (pairFst (pairSnd row)) (pairSnd (pairSnd row))) before))
  change (polynomialSignedAdd (polynomialSignedMultiply (pairFst row) previous)
    (polynomialSignedNeg
      (polynomialSignedMultiply (polynomialSignedMultiply (pairFst (pairSnd row)) (pairSnd (pairSnd row))) before))).length ≤ _
  simp only [List.length_tail] at hx hc hy hn hs
  omega

theorem integer_continuant_next_cobham :
    Cobham fun v : Fin 3 → List Bool => integerContinuantNext (v 0) (v 1) (v 2) := by
  have hd := Cobham.fstBlockFn (Cobham.proj (0 : Fin 3))
  have hl := Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 3)))
  have hu := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.proj (0 : Fin 3)))
  have hx := Cobham.comp₂ polynomial_signed_multiply_cobham hd (.proj 1)
  have hc := Cobham.comp₂ polynomial_signed_multiply_cobham hl hu
  have hy := Cobham.comp₂ polynomial_signed_multiply_cobham hc (.proj 2)
  have hn := Cobham.comp polynomial_signed_neg_cobham fun _ : Fin 1 => hy
  exact (Cobham.comp₂ polynomial_signed_add_cobham hx hn).of_eq fun _ => rfl

theorem integer_continuant_pack_cobham {n : ℕ}
    {rest previous before : (Fin n → List Bool) → List Bool}
    (hr : Cobham rest) (hp : Cobham previous) (hb : Cobham before) :
    Cobham fun v => integerContinuantPack (rest v) (previous v) (before v) :=
  (Cobham.comp₂ Cobham.pairing hr (Cobham.comp₂ Cobham.pairing hp hb)).of_eq fun _ => rfl

theorem integer_continuant_step_pack (rest previous before : List Bool) :
    integerContinuantStep (integerContinuantPack rest previous before)=
      if rest=[] then integerContinuantPack rest previous before else
        integerContinuantPack (pairSnd rest) (integerContinuantNext (pairFst rest) previous before) previous := by
  simp only [integerContinuantStep,integerContinuantRest,integerContinuantPrevious,integerContinuantBefore,
    integerContinuantPack,pairFst_pair,pairSnd_pair]
  cases rest <;> simp [nonemptyFlag,caseBit,caseBit₀]

theorem integer_continuant_step_cobham :
    Cobham fun v : Fin 1 → List Bool => integerContinuantStep (v 0) := by
  have hr : Cobham fun v : Fin 1 → List Bool => integerContinuantRest (v 0) := Cobham.fstBlockFn (.proj 0)
  have hp : Cobham fun v : Fin 1 → List Bool => integerContinuantPrevious (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0))
  have hb : Cobham fun v : Fin 1 → List Bool => integerContinuantBefore (v 0) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0))
  let args : Fin 3 → (Fin 1 → List Bool) → List Bool :=
    ![fun v => pairFst (integerContinuantRest (v 0)),fun v => integerContinuantPrevious (v 0),
      fun v => integerContinuantBefore (v 0)]
  have ha : ∀ i, Cobham (args i) := by
    intro i
    fin_cases i
    · simpa [args] using Cobham.fstBlockFn hr
    · simpa [args] using hp
    · simpa [args] using hb
  have hn := Cobham.comp integer_continuant_next_cobham ha
  exact (Cobham.iteFn (Cobham.nonemptyFn hr)
    (integer_continuant_pack_cobham (Cobham.sndBlockFn hr) hn hp) (Cobham.proj 0)).of_eq fun _ => rfl

theorem integer_continuant_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => integerContinuantInitial (v 0) :=
  (integer_continuant_pack_cobham (Cobham.proj (0 : Fin 1))
    (Cobham.const [false,true]) (Cobham.const [false])).of_eq fun _ => rfl

#print axioms integer_continuant_step_cobham
end IV04.Paper.Computational
