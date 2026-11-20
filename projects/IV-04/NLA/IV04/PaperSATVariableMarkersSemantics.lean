module

public import NLA.IV04.PaperSATVariableMarkersPoly
public import NLA.IV04.PaperSATLiteralMatchSemantics
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
private theorem variable_marker_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr];exact IV04.Paper.bits_foldr n
 theorem variable_marker_digit_nat (i v : ℕ) :
    variableMarkerDigit i.bits v.bits=(if i=v then [true] else []) := by
  by_cases h : i=v <;>
    simp [variableMarkerDigit,literal_match_flag_raw,pairFst_pair,pairSnd_pair,
      variable_marker_bits_value,firstBit,h,caseBit₀,caseBit]
 theorem variable_marker_step_nat (i bound v : ℕ) (output : List Bool) :
    variableMarkerStep (variableMarkerPack i.bits bound.bits v.bits output)=
      if i<bound then variableMarkerPack (i+1).bits bound.bits v.bits
        (pair (if i=v then [true] else []) output) else variableMarkerPack i.bits bound.bits v.bits output := by
  rw [variable_marker_step_pair,polynomial_word_le_value]
  simp only [variable_marker_bits_value]
  by_cases h : i<bound
  · simp [h,Nat.not_le_of_gt h,notBit,caseBit₀,caseBit,canonical_word_eq_bits,
      polynomial_word_add_value,variable_marker_bits_value,wordValue,bitValue,variable_marker_digit_nat]
  · simp [h,Nat.le_of_not_gt h,notBit,caseBit₀,caseBit]
 theorem variable_marker_iterate_inactive (k i bound v : ℕ) (output : List Bool) (h : bound ≤ i) :
    (variableMarkerStep^[k]) (variableMarkerPack i.bits bound.bits v.bits output)=
      variableMarkerPack i.bits bound.bits v.bits output := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply',ih,variable_marker_step_nat];simp [Nat.not_lt.mpr h]
 theorem variable_marker_iteration_code (k i bound v : ℕ) (output : List (List Bool))
    (hi : i ≤ bound) (hclock : bound-i ≤ k) :
    (variableMarkerStep^[k]) (variableMarkerPack i.bits bound.bits v.bits (payloadListCode output))=
      variableMarkerPack bound.bits bound.bits v.bits
        (payloadListCode (((List.range' i (bound-i)).map fun j => if j=v then [true] else []).reverse ++ output)) := by
  induction k generalizing i output with
  | zero =>
    have he : i=bound := by omega
    subst i
    simp [payloadListCode]
  | succ k ih =>
    by_cases he : i=bound
    · subst i
      rw [variable_marker_iterate_inactive (k+1) bound bound v _ (le_refl _)]
      simp
    · have hil : i<bound := by omega
      have hc : bound-(i+1) ≤ k := by omega
      have hs : bound-i=(bound-(i+1))+1 := by omega
      rw [Function.iterate_succ_apply,variable_marker_step_nat]
      simp only [hil,if_true]
      have ht := ih (i+1) ((if i=v then [true] else [])::output) (by omega) hc
      simp only [payloadListCode] at ht
      rw [ht]
      rw [hs,List.range'_succ]
      simp [List.reverse_cons,List.append_assoc]
 theorem polynomial_sat_variable_markers_exact (ruler : List Bool) (bound v : ℕ)
    (h : bound ≤ ruler.length+1) :
    polynomialSATVariableMarkers (pair ruler (pair bound.bits v.bits))=
      payloadListCode (((List.range bound).map fun i => if i=v then [true] else []).reverse) := by
  have hi := variable_marker_iteration_code (ruler.length+1) 0 bound v [] (Nat.zero_le _) (by simpa using h)
  have hz : (0 : ℕ).bits=[] := rfl
  simpa only [polynomialSATVariableMarkers,variableMarkerState,pairFst_pair,pairSnd_pair,
    variableMarkerPack,payloadListCode,hz,Nat.sub_zero,List.range_eq_range',List.append_nil]
      using congrArg (fun s => pairSnd (pairSnd (pairSnd s))) hi
 theorem sat_variable_markers_actual_polytime : polynomialSATVariableMarkers ∈ FP ∧
    (∀ input, (polynomialSATVariableMarkers input).length ≤ 10*input.length+14) ∧
    (∀ (ruler : List Bool) (bound v : ℕ), bound ≤ ruler.length+1 →
      polynomialSATVariableMarkers (pair ruler (pair bound.bits v.bits))=
        payloadListCode (((List.range bound).map fun i => if i=v then [true] else []).reverse)) :=
  ⟨polynomial_sat_variable_markers_mem_fp,polynomial_sat_variable_markers_length,
    polynomial_sat_variable_markers_exact⟩
#print axioms polynomial_sat_variable_markers_exact
#print axioms sat_variable_markers_actual_polytime
end IV04.Paper.Computational
