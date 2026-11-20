module

public import NLA.IV04.PaperWordAdderSemantics
public import NLA.IV04.Complexitylib.Classes.Containments.Internal.FPBridge
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity Complexity.Cobham
namespace IV04.Paper.Computational

theorem xor_flag_cobham {n : ℕ} {left right : (Fin n → List Bool) → List Bool}
    (hl : Cobham left) (hr : Cobham right) :
    Cobham fun v => xorFlag (left v) (right v) :=
  Cobham.iteFn hl (Cobham.notFn hr) hr

theorem adder_pack_cobham {n : ℕ}
    {left right carry output : (Fin n → List Bool) → List Bool}
    (hl : Cobham left) (hr : Cobham right) (hc : Cobham carry) (ho : Cobham output) :
    Cobham fun v => adderPack (left v) (right v) (carry v) (output v) := by
  exact (Cobham.comp₂ Cobham.pairing hl
    (Cobham.comp₂ Cobham.pairing hr (Cobham.comp₂ Cobham.pairing hc ho))).of_eq fun v => by
      simp [adderPack]

theorem word_adder_step_cobham : Cobham fun v : Fin 1 → List Bool => wordAdderStep (v 0) := by
  have hl : Cobham fun v : Fin 1 → List Bool => adderLeft (v 0) :=
    Cobham.fstBlockFn (.proj 0)
  have hr : Cobham fun v : Fin 1 → List Bool => adderRight (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (.proj 0))
  have hc : Cobham fun v : Fin 1 → List Bool => adderCarry (v 0) :=
    Cobham.fstBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0)))
  have ho : Cobham fun v : Fin 1 → List Bool => adderOutput (v 0) :=
    Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn (.proj 0)))
  have ha := Cobham.headFlagFn hl
  have hb := Cobham.headFlagFn hr
  have hs := xor_flag_cobham (xor_flag_cobham ha hb) hc
  have hn := Cobham.orFn (Cobham.andFn ha hb) (Cobham.andFn hc (Cobham.orFn ha hb))
  have ht : Cobham fun v : Fin 1 → List Bool => true :: adderOutput (v 0) :=
    (Cobham.comp (.bit true) fun _ : Fin 1 => ho).of_eq fun _ => rfl
  have hf : Cobham fun v : Fin 1 → List Bool => false :: adderOutput (v 0) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => ho).of_eq fun _ => rfl
  have hout := Cobham.iteFn hs ht hf
  exact (adder_pack_cobham (Cobham.tailFn hl) (Cobham.tailFn hr) hn hout).of_eq fun _ => rfl

theorem word_adder_state_cobham :
    Cobham fun v : Fin 2 → List Bool =>
      (wordAdderStep^[(v 0).length+(v 1).length+1]) (adderPack (v 0) (v 1) [false] []) := by
  let initial : (Fin 2 → List Bool) → List Bool :=
    fun v => adderPack (v 0) (v 1) [false] []
  let step : (Fin 3 → List Bool) → List Bool := fun v => wordAdderStep (v 0)
  let ruler : (Fin 3 → List Bool) → List Bool :=
    fun v => v 0 ++ v 1 ++ v 1 ++ v 2 ++ v 2 ++ List.replicate 8 false
  have he : Cobham initial := adder_pack_cobham (.proj 0) (.proj 1) (.const [false]) (.const [])
  have hs : Cobham step :=
    (Cobham.comp word_adder_step_cobham fun _ : Fin 1 => .proj 0).of_eq fun _ => rfl
  have hj : Cobham ruler :=
    Cobham.appendFn (Cobham.appendFn (Cobham.appendFn
      (Cobham.appendFn (Cobham.appendFn (.proj 0) (.proj 1)) (.proj 1)) (.proj 2)) (.proj 2))
      (.const (List.replicate 8 false))
  have hbound : ∀ (clock : List Bool) (v : Fin 2 → List Bool),
      ((fun s => step (Fin.cons s v))^[clock.length] (initial v)).length ≤
        (ruler (Fin.cons clock v)).length := by
    intro clock v
    change ((wordAdderStep^[clock.length]) (adderPack (v 0) (v 1) [false] [])).length ≤ _
    rw [wordAdder_iterate_run]
    have h := adderRun_length clock.length (v 0) (v 1) [] false
    simp only [ruler,List.length_append,List.length_replicate,Fin.cons_zero] at *
    change (adderRun clock.length (v 0) (v 1) false []).length ≤
      clock.length+(v 0).length+(v 0).length+(v 1).length+(v 1).length+8
    simp only [List.length_nil] at h
    omega
  have hi := Cobham.iterFn he hs hj hbound
  let arguments : Fin 3 → (Fin 2 → List Bool) → List Bool :=
    ![fun v => false :: (v 0 ++ v 1),fun v => v 0,fun v => v 1]
  have hc : Cobham fun v : Fin 2 → List Bool => false :: (v 0 ++ v 1) :=
    (Cobham.comp (.bit false) fun _ : Fin 1 => Cobham.appendFn (.proj 0) (.proj 1)).of_eq fun _ => rfl
  have hargs : ∀ i, Cobham (arguments i) := by
    intro i
    fin_cases i
    · simpa [arguments] using hc
    · simpa [arguments] using (Cobham.proj 0 : Cobham fun v : Fin 2 → List Bool => v 0)
    · simpa [arguments] using (Cobham.proj 1 : Cobham fun v : Fin 2 → List Bool => v 1)
  refine (Cobham.comp hi hargs).of_eq fun v => ?_
  simp [arguments,initial,step,Fin.tail,List.length_append]

theorem polynomial_word_add_cobham :
    Cobham fun v : Fin 2 → List Bool => polynomialWordAdd (v 0) (v 1) := by
  have ho := Cobham.sndBlockFn (Cobham.sndBlockFn (Cobham.sndBlockFn word_adder_state_cobham))
  have hr : Cobham fun v : Fin 1 → List Bool => (v 0).reverse :=
    FP_subset_CobhamFP reverse_mem_FP
  exact (Cobham.comp hr fun _ : Fin 1 => ho).of_eq fun _ => rfl

theorem encoded_word_add_mem_fp : encodedPolynomialWordAdd ∈ FP := by
  have h := Cobham.comp₂ polynomial_word_add_cobham
    (Cobham.fstBlockFn (Cobham.proj (0 : Fin 1))) (Cobham.sndBlockFn (Cobham.proj (0 : Fin 1)))
  exact CobhamFP_subset_FP (h.of_eq fun v => by simp [encodedPolynomialWordAdd])

theorem encoded_word_add_actual_polytime : encodedPolynomialWordAdd ∈ FP ∧
    ∀ left right, wordValue (encodedPolynomialWordAdd (Complexity.pair left right))=
      wordValue left+wordValue right := by
  refine ⟨encoded_word_add_mem_fp,?_⟩
  intro left right
  simpa [encodedPolynomialWordAdd] using polynomial_word_add_value left right

#print axioms encoded_word_add_actual_polytime
end IV04.Paper.Computational
