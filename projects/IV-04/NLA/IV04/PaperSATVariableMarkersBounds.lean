module

public import NLA.IV04.PaperSATVariableMarkersDefinitions
public import NLA.IV04.PaperSATLiteralMatchPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
 theorem variable_marker_pack_length (index bound query output : List Bool) :
    (variableMarkerPack index bound query output).length=
      2*index.length+2*bound.length+2*query.length+output.length+6 := by
  simp only [variableMarkerPack,pair_length];omega
 theorem variable_marker_digit_length (index query : List Bool) :
    (variableMarkerDigit index query).length ≤ 1 := by
  exact case_bit_zero_property (P:=fun bits => bits.length ≤ 1)
    (literalMatchFlag (pair index [false]) (pair query [false])) [true] [] (by simp) (by simp)
 theorem variable_marker_step_pair (index bound query output : List Bool) :
    variableMarkerStep (variableMarkerPack index bound query output)=
      caseBit₀ (notBit (polynomialWordLe bound index))
        (variableMarkerPack (canonicalWord (polynomialWordAdd index [true])) bound query
          (pair (variableMarkerDigit index query) output)) (variableMarkerPack index bound query output) := by
  simp only [variableMarkerStep,variableMarkerPack,pairFst_pair,pairSnd_pair]
 theorem variable_marker_step_shape (index bound query output : List Bool) :
    ∃ i o : List Bool, variableMarkerStep (variableMarkerPack index bound query output)=
      variableMarkerPack i bound query o ∧
      (variableMarkerPack i bound query o).length ≤ (variableMarkerPack index bound query output).length+8 := by
  rw [variable_marker_step_pair]
  by_cases hl : wordValue bound ≤ wordValue index
  · refine ⟨index,output,?_,by omega⟩
    simp [polynomial_word_le_value,hl,notBit,caseBit₀,caseBit]
  · refine ⟨canonicalWord (polynomialWordAdd index [true]),
      pair (variableMarkerDigit index query) output,?_,?_⟩
    · simp [polynomial_word_le_value,hl,notBit,caseBit₀,caseBit]
    · have hc := canonical_word_length (polynomialWordAdd index [true])
      have ha := polynomial_word_add_length index [true]
      have hd := variable_marker_digit_length index query
      simp only [variable_marker_pack_length,pair_length,List.length_cons,List.length_nil] at ha ⊢
      omega
 theorem variable_marker_iterate_shape (k : ℕ) (index bound query output : List Bool) :
    ∃ i o : List Bool, (variableMarkerStep^[k]) (variableMarkerPack index bound query output)=
      variableMarkerPack i bound query o ∧
      (variableMarkerPack i bound query o).length ≤ (variableMarkerPack index bound query output).length+8*k := by
  induction k with
  | zero => exact ⟨index,output,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨i,o,he,hb⟩ := ih
    obtain ⟨i',o',hs,hl⟩ := variable_marker_step_shape i bound query o
    refine ⟨i',o',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega
 theorem variable_marker_clock_length (clock input : List Bool) :
    ((variableMarkerStep^[clock.length])
      (variableMarkerPack [] (pairFst (pairSnd input)) (pairSnd (pairSnd input)) [])).length ≤
        2*input.length+6+8*clock.length := by
  obtain ⟨i,o,he,hb⟩ := variable_marker_iterate_shape clock.length [] (pairFst (pairSnd input)) (pairSnd (pairSnd input)) []
  have hp := pair_projection_budget (pairSnd input)
  have hq := pairSnd_length_le input
  rw [he,variable_marker_pack_length]
  simp only [variable_marker_pack_length,List.length_nil] at hb
  omega
 theorem polynomial_sat_variable_markers_length (input : List Bool) :
    (polynomialSATVariableMarkers input).length ≤ 10*input.length+14 := by
  have hs := variable_marker_clock_length (false::pairFst input) input
  have hc := pairFst_length_le input
  have hp := pairSnd_length_le (variableMarkerState input)
  have hq := pairSnd_length_le (pairSnd (variableMarkerState input))
  have hr := pairSnd_length_le (pairSnd (pairSnd (variableMarkerState input)))
  simp only [List.length_cons] at hs
  unfold polynomialSATVariableMarkers
  unfold variableMarkerState at hp hq hr ⊢
  omega
end IV04.Paper.Computational
