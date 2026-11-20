module

public import NLA.IV04.PaperBoundedPayloadRepeatDefinitions
public import NLA.IV04.PaperSATVariableMarkersBounds
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
 theorem bounded_payload_repeat_step_pair (index bound coefficient output : List Bool) :
    boundedPayloadRepeatStep (variableMarkerPack index bound coefficient output)=
      caseBit₀ (notBit (polynomialWordLe bound index))
        (variableMarkerPack (canonicalWord (polynomialWordAdd index [true])) bound coefficient
          (pair coefficient output)) (variableMarkerPack index bound coefficient output) := by
  simp only [boundedPayloadRepeatStep,variableMarkerPack,pairFst_pair,pairSnd_pair]
 theorem bounded_payload_repeat_step_shape (index bound coefficient output : List Bool) :
    ∃ i o : List Bool, boundedPayloadRepeatStep (variableMarkerPack index bound coefficient output)=
      variableMarkerPack i bound coefficient o ∧
      (variableMarkerPack i bound coefficient o).length ≤
        (variableMarkerPack index bound coefficient output).length+2*coefficient.length+8 := by
  rw [bounded_payload_repeat_step_pair]
  by_cases hl : wordValue bound ≤ wordValue index
  · refine ⟨index,output,?_,by omega⟩
    simp [polynomial_word_le_value,hl,notBit,caseBit₀]
  · refine ⟨canonicalWord (polynomialWordAdd index [true]),pair coefficient output,?_,?_⟩
    · simp [polynomial_word_le_value,hl,notBit,caseBit₀]
    · have hc := canonical_word_length (polynomialWordAdd index [true])
      have ha := polynomial_word_add_length index [true]
      simp only [variable_marker_pack_length,pair_length,List.length_cons,List.length_nil] at ha ⊢
      omega
 theorem bounded_payload_repeat_iterate_shape (k : ℕ) (index bound coefficient output : List Bool) :
    ∃ i o : List Bool, (boundedPayloadRepeatStep^[k]) (variableMarkerPack index bound coefficient output)=
      variableMarkerPack i bound coefficient o ∧
      (variableMarkerPack i bound coefficient o).length ≤
        (variableMarkerPack index bound coefficient output).length+(2*coefficient.length+8)*k := by
  induction k with
  | zero => exact ⟨index,output,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨i,o,he,hb⟩ := ih
    obtain ⟨i',o',hs,hl⟩ := bounded_payload_repeat_step_shape i bound coefficient o
    refine ⟨i',o',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · nlinarith
 theorem bounded_payload_repeat_clock_length (clock input : List Bool) :
    ((boundedPayloadRepeatStep^[clock.length])
      (variableMarkerPack [] (pairFst (pairSnd input)) (pairSnd (pairSnd input)) [])).length ≤
        2*input.length+6+(2*input.length+8)*clock.length := by
  obtain ⟨i,o,he,hb⟩ := bounded_payload_repeat_iterate_shape clock.length []
    (pairFst (pairSnd input)) (pairSnd (pairSnd input)) []
  have hp := pair_projection_budget (pairSnd input)
  have hq := pairSnd_length_le input
  have hc := pairSnd_length_le (pairSnd input)
  have hm := Nat.mul_le_mul_right clock.length
    (show 2*(pairSnd (pairSnd input)).length+8 ≤ 2*input.length+8 by omega)
  rw [he,variable_marker_pack_length]
  simp only [variable_marker_pack_length,List.length_nil] at hb
  omega
 theorem polynomial_bounded_payload_repeat_length (input : List Bool) :
    (polynomialBoundedPayloadRepeat input).length ≤
      2*input.length+6+(2*input.length+8)*(input.length+1) := by
  have hs := bounded_payload_repeat_clock_length (false::pairFst input) input
  have hc := pairFst_length_le input
  have hm := Nat.mul_le_mul_left (2*input.length+8)
    (show (false::pairFst input).length ≤ input.length+1 by simp only [List.length_cons];omega)
  have hp := pairSnd_length_le (boundedPayloadRepeatState input)
  have hq := pairSnd_length_le (pairSnd (boundedPayloadRepeatState input))
  have hr := pairSnd_length_le (pairSnd (pairSnd (boundedPayloadRepeatState input)))
  simp only [List.length_cons] at hs hm
  unfold polynomialBoundedPayloadRepeat
  unfold boundedPayloadRepeatState at hp hq hr ⊢
  omega
#print axioms bounded_payload_repeat_clock_length
#print axioms polynomial_bounded_payload_repeat_length
end IV04.Paper.Computational
