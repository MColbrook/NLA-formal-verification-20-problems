module

public import NLA.IV04.PaperIntegerContinuantMachineStep
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem integer_continuant_step_shape (rest previous before : List Bool) :
    ∃ r p b : List Bool,
      integerContinuantStep (integerContinuantPack rest previous before)=integerContinuantPack r p b ∧
      r.length+max p.length b.length ≤ rest.length+max previous.length before.length+4 := by
  rw [integer_continuant_step_pack]
  split_ifs with he
  · exact ⟨rest,previous,before,rfl,by omega⟩
  · refine ⟨_,_,_,rfl,?_⟩
    have hp := pair_projection_budget rest
    have hn := integer_continuant_next_length (pairFst rest) previous before
    omega

theorem integer_continuant_iterate_shape (k : ℕ) (rest previous before : List Bool) :
    ∃ r p b : List Bool,
      (integerContinuantStep^[k]) (integerContinuantPack rest previous before)=integerContinuantPack r p b ∧
      r.length+max p.length b.length ≤ rest.length+max previous.length before.length+4*k := by
  induction k with
  | zero => exact ⟨rest,previous,before,rfl,by omega⟩
  | succ k ih =>
    obtain ⟨r,p,b,he,hb⟩ := ih
    obtain ⟨r',p',b',hs,hb'⟩ := integer_continuant_step_shape r p b
    refine ⟨r',p',b',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

theorem integer_continuant_pack_length (rest previous before : List Bool) :
    (integerContinuantPack rest previous before).length ≤
      3*(rest.length+max previous.length before.length)+4 := by
  simp only [integerContinuantPack,pair_length]
  omega

theorem integer_continuant_iterate_length (k : ℕ) (rest previous before : List Bool) :
    ((integerContinuantStep^[k]) (integerContinuantPack rest previous before)).length ≤
      3*(rest.length+max previous.length before.length)+4+12*k := by
  obtain ⟨r,p,b,he,hb⟩ := integer_continuant_iterate_shape k rest previous before
  rw [he]
  have hl := integer_continuant_pack_length r p b
  omega

theorem integer_continuant_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((integerContinuantStep^[k]) (integerContinuantInitial input)).length ≤ 3*input.length+10+12*k := by
  have h := integer_continuant_iterate_length k input [false,true] [false]
  simp only [List.length_cons,List.length_nil] at h
  change ((integerContinuantStep^[k]) (integerContinuantPack input [false,true] [false])).length ≤ _
  omega

theorem integer_continuant_state_length (input : List Bool) :
    (integerContinuantState input).length ≤ 15*input.length+10 := by
  have h := integer_continuant_initial_iterate_length input.length input
  change ((integerContinuantStep^[input.length]) (integerContinuantInitial input)).length ≤ _
  omega

#print axioms integer_continuant_state_length
end IV04.Paper.Computational
