module

public import NLA.IV04.PaperVertexSelectionDefinitions
public import NLA.IV04.PaperCountedMachineStep
public import NLA.IV04.PaperSignedOrderPoly
public import NLA.IV04.PaperWordListProductBounds
public import NLA.IV04.PaperSignedWordBounds
public import NLA.IV04.PaperCountedOutputSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem vertex_selection_pack_cobham {n : ℕ}
    {count flag fields choices output : (Fin n → List Bool) → List Bool}
    (hc : Cobham count) (hf : Cobham flag) (ht : Cobham fields)
    (hb : Cobham choices) (ho : Cobham output) :
    Cobham fun v => vertexSelectionPack (count v) (flag v) (fields v) (choices v) (output v) :=
  (Cobham.comp₂ Cobham.pairing hc (Cobham.comp₂ Cobham.pairing hf
    (Cobham.comp₂ Cobham.pairing ht (Cobham.comp₂ Cobham.pairing hb ho)))).of_eq fun _ => rfl

theorem vertex_selection_ready_cobham :
    Cobham fun v : Fin 2 → List Bool => vertexSelectionReady (v 0) (v 1) := by
  have hf := Cobham.proj (0 : Fin 2)
  have hc := Cobham.proj (1 : Fin 2)
  have hs := Cobham.comp₂ polynomial_signed_le_cobham (Cobham.fstBlockFn hf)
    (Cobham.fstBlockFn (Cobham.sndBlockFn hf))
  exact (Cobham.andFn (Cobham.nonemptyFn hf)
    (Cobham.andFn (Cobham.nonemptyFn (Cobham.sndBlockFn hf))
      (Cobham.andFn (Cobham.nonemptyFn hc) hs))).of_eq fun _ => rfl

theorem vertex_selected_word_cobham :
    Cobham fun v : Fin 2 → List Bool => vertexSelectedWord (v 0) (v 1) :=
  (Cobham.iteFn (.proj 1) (Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0)))
    (Cobham.fstBlockFn (.proj 0))).of_eq fun _ => rfl

theorem vertex_selected_word_length (fields choices : List Bool) :
    (vertexSelectedWord fields choices).length ≤
      (pairFst fields).length+(pairFst (pairSnd fields)).length := by
  unfold vertexSelectedWord
  apply case_bit_zero_property (P:=fun bits => bits.length ≤
    (pairFst fields).length+(pairFst (pairSnd fields)).length) <;> omega

theorem vertex_selected_word_value (lower upper rest : List Bool) (choice : Bool) (choices : List Bool) :
    signedWordValue (vertexSelectedWord (pair lower (pair upper rest)) (choice::choices))=
      if choice then signedWordValue upper else signedWordValue lower := by
  cases choice <;> simp [vertexSelectedWord,pairFst_pair,pairSnd_pair,caseBit₀]

theorem vertex_selection_pair_nonempty_flag (left right : List Bool) :
    nonemptyFlag (pair left right)=[true] := by
  have h := payload_pair_ne_nil left right
  cases he : pair left right <;> simp_all [nonemptyFlag]

theorem vertex_selection_ready_pair (lower upper rest : List Bool) (choice : Bool) (choices : List Bool) :
    vertexSelectionReady (pair lower (pair upper rest)) (choice::choices)=
      [decide (signedWordValue lower ≤ signedWordValue upper)] := by
  have hc : nonemptyFlag (choice::choices)=[true] := by cases choice <;> rfl
  simp only [vertexSelectionReady,pairFst_pair,pairSnd_pair,
    vertex_selection_pair_nonempty_flag,hc,polynomial_signed_le_value]
  cases decide (signedWordValue lower ≤ signedWordValue upper) <;> rfl

theorem vertex_selection_step_pack (count flag fields choices output : List Bool) :
    vertexSelectionStep (vertexSelectionPack count flag fields choices output)=
      caseBit₀ (nonemptyFlag (canonicalWord count))
        (caseBit₀ flag (caseBit₀ (vertexSelectionReady fields choices)
          (vertexSelectionPack (decrementCount count) [true] (pairSnd (pairSnd fields))
            choices.tail (pair (vertexSelectedWord fields choices) output))
          (vertexSelectionPack count [false] fields choices output))
          (vertexSelectionPack count flag fields choices output))
        (vertexSelectionPack count flag fields choices output) := by
  simp only [vertexSelectionStep,vertexSelectionCount,vertexSelectionFlag,vertexSelectionFields,
    vertexSelectionChoices,vertexSelectionOutput,vertexSelectionPack,pairFst_pair,pairSnd_pair]

set_option maxHeartbeats 2000000 in
theorem vertex_selection_step_cobham :
    Cobham fun v : Fin 1 → List Bool => vertexSelectionStep (v 0) := by
  have hc : Cobham fun v : Fin 1 → List Bool => vertexSelectionCount (v 0) := Cobham.fstBlockFn (.proj 0)
  have hf : Cobham fun v : Fin 1 → List Bool => vertexSelectionFlag (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0))
  have ht : Cobham fun v : Fin 1 → List Bool => vertexSelectionFields (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0)))
  have hb : Cobham fun v : Fin 1 → List Bool => vertexSelectionChoices (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0))))
  have ho : Cobham fun v : Fin 1 → List Bool => vertexSelectionOutput (v 0) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0))))
  have hd := Cobham.comp decrement_count_cobham fun _ : Fin 1 => hc
  have hs := Cobham.comp₂ vertex_selected_word_cobham ht hb
  have hr := Cobham.comp₂ vertex_selection_ready_cobham ht hb
  have hy := vertex_selection_pack_cobham hd (Cobham.const [true])
    (Cobham.sndBlockFn (Cobham.sndBlockFn ht)) (Cobham.tailFn hb)
    (Cobham.comp₂ Cobham.pairing hs ho)
  have hn := vertex_selection_pack_cobham hc (Cobham.const [false]) ht hb ho
  have hp := Cobham.nonemptyFn (Cobham.comp canonical_word_cobham fun _ : Fin 1 => hc)
  exact (Cobham.iteFn hp (Cobham.iteFn hf (Cobham.iteFn hr hy hn) (.proj 0)) (.proj 0)).of_eq fun _ => rfl

theorem vertex_selection_initial_cobham :
    Cobham fun v : Fin 1 → List Bool => vertexSelectionInitial (v 0) := by
  exact (vertex_selection_pack_cobham
    (Cobham.comp canonical_word_cobham fun _ : Fin 1 => Cobham.fstBlockFn (.proj 0))
    (Cobham.const [true]) (Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0)))
    (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0))) (Cobham.const [])).of_eq fun _ => rfl

#print axioms vertex_selection_step_cobham
end IV04.Paper.Computational
