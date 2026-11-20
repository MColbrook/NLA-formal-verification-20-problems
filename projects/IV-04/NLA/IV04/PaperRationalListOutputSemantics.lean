module

public import NLA.IV04.PaperRationalListOutputDefinitions
public import NLA.IV04.PaperRationalListMachineBounds
public import NLA.IV04.PaperRationalListReference
public import NLA.IV04.PaperCountedOutputSemantics
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem decode_fraction_payloads_code (fuel : ℕ) (payloads : List (List Bool))
    (h : (payloadListCode payloads).length ≤ fuel) :
    decodeFractionPayloads fuel (payloadListCode payloads)=payloads.map fractionWordValue := by
  induction payloads generalizing fuel with
  | nil => cases fuel <;> simp [decodeFractionPayloads,payloadListCode]
  | cons payload payloads ih =>
    cases fuel with
    | zero => simp [payloadListCode] at h
    | succ fuel =>
      have ht : (payloadListCode payloads).length ≤ fuel := by
        simp only [payloadListCode,Complexity.pair_length] at h
        omega
      simp [decodeFractionPayloads,payloadListCode,payload_pair_ne_nil,ih fuel ht]

theorem rational_list_state_result_pack (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    rationalListStateResult (countedPack count [valid] rest (payloadListCode payloads))=
      if wordValue count=0 ∧ valid=true then some ((payloads.map fractionWordValue).reverse,rest) else none := by
  have hd := decode_fraction_payloads_code (payloadListCode payloads).length payloads (le_refl _)
  simp only [rationalListStateResult,countedCount,countedFlag,countedOutput,countedRest,countedPack,
    Complexity.pairFst_pair,Complexity.pairSnd_pair,hd,List.cons.injEq,and_true]

set_option maxHeartbeats 2000000 in
theorem rational_list_iterate_run (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    (rationalListStep^[fuel]) (countedPack count [valid] rest (payloadListCode payloads))=
      rationalListRun fuel count valid rest payloads := by
  induction fuel generalizing count rest valid payloads with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply,rational_list_step_pack]
    simp only [rationalListRun]
    split_ifs with hz hv hp
    · exact ih count rest valid payloads
    · exact ih (decrementCount count)
        (Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser rest))) true
        (Complexity.pairFst (Complexity.pairSnd (encodedRationalParser rest)) :: payloads)
    · exact ih count rest false payloads
    · exact ih count rest valid payloads

theorem read_rational_of_flag_true (input : List Bool)
    (h : Complexity.pairFst (encodedRationalParser input)=[true]) :
    IV04.Paper.readRational input=some
      (fractionWordValue (Complexity.pairFst (Complexity.pairSnd (encodedRationalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser input))) := by
  rw [←rational_parser_exact]
  simp only [h,if_true]

theorem read_rational_of_flag_false (input : List Bool)
    (h : Complexity.pairFst (encodedRationalParser input)=[false]) :
    IV04.Paper.readRational input=none := by
  rw [←rational_parser_exact]
  simp [h]

set_option maxHeartbeats 2000000 in
theorem rational_list_run_result (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    rationalListStateResult (rationalListRun fuel count valid rest payloads)=
      if valid then (fuelReadRationals fuel (wordValue count) rest).map
        (fun x => ((payloads.map fractionWordValue).reverse ++ x.1,x.2)) else none := by
  induction fuel generalizing count rest valid payloads with
  | zero =>
    rw [rationalListRun,rational_list_state_result_pack]
    cases hn : wordValue count <;> cases valid <;> simp [fuelReadRationals,hn]
  | succ fuel ih =>
    cases hn : wordValue count with
    | zero =>
      simp [rationalListRun,hn,ih,fuelReadRationals]
    | succ n =>
      cases valid with
      | false => simp [rationalListRun,hn,ih]
      | true =>
        obtain hp | hp := rational_parser_flag_boolean rest
        · have hr := read_rational_of_flag_true rest hp
          simp only [rationalListRun,hn,Nat.succ_ne_zero,if_false,if_true,hp]
          rw [ih]
          simp only [decrement_count_value,hn,Nat.add_sub_cancel,fuelReadRationals,hr,
            Option.bind_some,Option.pure_def,Option.map_some]
          cases he : fuelReadRationals fuel n
            (Complexity.pairSnd (Complexity.pairSnd (encodedRationalParser rest))) with
          | none => simp [he]
          | some parsed =>
            obtain ⟨values,tail⟩ := parsed
            simp [he,List.reverse_cons,List.append_assoc]
        · have hr := read_rational_of_flag_false rest hp
          simp [rationalListRun,hn,hp,ih,fuelReadRationals,hr]

#print axioms rational_list_run_result
end IV04.Paper.Computational
