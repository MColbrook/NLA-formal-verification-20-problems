module

public import NLA.IV04.PaperCountedOutputDefinitions
public import NLA.IV04.PaperCountedMachineBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem payload_pair_ne_nil (payload output : List Bool) : Complexity.pair payload output ≠ [] := by
  intro h
  have hl := congrArg List.length h
  simp only [Complexity.pair_length,List.length_nil] at hl
  omega

theorem decode_payloads_code (fuel : ℕ) (payloads : List (List Bool))
    (h : (payloadListCode payloads).length ≤ fuel) :
    decodePayloads fuel (payloadListCode payloads)=payloads.map wordValue := by
  induction payloads generalizing fuel with
  | nil => cases fuel <;> simp [decodePayloads,payloadListCode]
  | cons payload payloads ih =>
    cases fuel with
    | zero => simp [payloadListCode] at h
    | succ fuel =>
      have ht : (payloadListCode payloads).length ≤ fuel := by
        simp only [payloadListCode,Complexity.pair_length] at h
        omega
      simp [decodePayloads,payloadListCode,payload_pair_ne_nil,ih fuel ht]

theorem counted_state_result_pack (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    countedStateResult (countedPack count [valid] rest (payloadListCode payloads))=
      if wordValue count=0 ∧ valid=true then some ((payloads.map wordValue).reverse,rest) else none := by
  have hd := decode_payloads_code (payloadListCode payloads).length payloads (le_refl _)
  simp only [countedStateResult,countedCount,countedFlag,countedOutput,countedRest,countedPack,
    Complexity.pairFst_pair,Complexity.pairSnd_pair,hd,List.cons.injEq,and_true]

set_option maxHeartbeats 2000000 in
theorem counted_iterate_run (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    (countedStep^[fuel]) (countedPack count [valid] rest (payloadListCode payloads))=
      countedRun fuel count valid rest payloads := by
  induction fuel generalizing count rest valid payloads with
  | zero => rfl
  | succ fuel ih =>
    rw [Function.iterate_succ_apply,counted_step_pack]
    simp only [countedRun]
    split_ifs with hz hv hp
    · exact ih count rest valid payloads
    · exact ih (decrementCount count)
        (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser rest))) true
        (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser rest)) :: payloads)
    · exact ih count rest false payloads
    · exact ih count rest valid payloads

theorem read_natural_of_flag_true (input : List Bool)
    (h : Complexity.pairFst (encodedNaturalParser input)=[true]) :
    IV04.Paper.readNatural input=some
      (wordValue (Complexity.pairFst (Complexity.pairSnd (encodedNaturalParser input))),
        Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser input))) := by
  rw [←natural_parser_exact]
  simp only [h,if_true]

theorem read_natural_of_flag_false (input : List Bool)
    (h : Complexity.pairFst (encodedNaturalParser input)=[false]) :
    IV04.Paper.readNatural input=none := by
  rw [←natural_parser_exact]
  simp [h]

set_option maxHeartbeats 2000000 in
theorem counted_run_result (fuel : ℕ) (count rest : List Bool) (valid : Bool)
    (payloads : List (List Bool)) :
    countedStateResult (countedRun fuel count valid rest payloads)=
      if valid then (fuelReadNaturals fuel (wordValue count) rest).map
        (fun x => ((payloads.map wordValue).reverse ++ x.1,x.2)) else none := by
  induction fuel generalizing count rest valid payloads with
  | zero =>
    rw [countedRun,counted_state_result_pack]
    cases hn : wordValue count <;> cases valid <;> simp [fuelReadNaturals,hn]
  | succ fuel ih =>
    cases hn : wordValue count with
    | zero =>
      simp [countedRun,hn,ih,fuelReadNaturals]
    | succ n =>
      cases valid with
      | false => simp [countedRun,hn,ih]
      | true =>
        obtain hp | hp := natural_parser_flag_boolean rest
        · have hr := read_natural_of_flag_true rest hp
          simp only [countedRun,hn,Nat.succ_ne_zero,if_false,if_true,hp]
          rw [ih]
          simp only [decrement_count_value,hn,Nat.add_sub_cancel,fuelReadNaturals,hr,
            Option.bind_some,Option.pure_def,Option.map_some]
          cases he : fuelReadNaturals fuel n
            (Complexity.pairSnd (Complexity.pairSnd (encodedNaturalParser rest))) with
          | none => simp [he]
          | some parsed =>
            obtain ⟨values,tail⟩ := parsed
            simp [he,List.reverse_cons,List.append_assoc]
        · have hr := read_natural_of_flag_false rest hp
          simp [countedRun,hn,hp,ih,fuelReadNaturals,hr]

#print axioms counted_run_result
end IV04.Paper.Computational
