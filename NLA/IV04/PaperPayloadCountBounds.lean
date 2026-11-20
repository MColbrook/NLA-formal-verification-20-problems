module

public import NLA.IV04.PaperPayloadCountDefinitions
public import NLA.IV04.PaperWordListProductBounds
public import NLA.IV04.PaperWordAdderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

 theorem payload_count_step_pair (rest count : List Bool) :
    payloadCountStep (pair rest count)=
      if rest=[] then pair rest count else pair (pairSnd rest) (polynomialWordAdd count [true]) := by
  simp only [payloadCountStep,pairFst_pair,pairSnd_pair]
  cases rest <;> simp [nonemptyFlag,caseBit₀,caseBit]

 theorem payload_count_step_shape (rest count : List Bool) :
    ∃ r c : List Bool, payloadCountStep (pair rest count)=pair r c ∧
      (pair r c).length ≤ (pair rest count).length+2 := by
  rw [payload_count_step_pair]
  split_ifs
  · exact ⟨rest,count,rfl,by omega⟩
  · refine ⟨_,_,rfl,?_⟩
    have hr := pairSnd_length_le rest
    have hc := polynomial_word_add_length count [true]
    simp only [pair_length,List.length_cons,List.length_nil] at hc ⊢
    omega

 theorem payload_count_iterate_shape (k : ℕ) (rest count : List Bool) :
    ∃ r c : List Bool, (payloadCountStep^[k]) (pair rest count)=pair r c ∧
      (pair r c).length ≤ (pair rest count).length+2*k := by
  induction k with
  | zero => exact ⟨rest,count,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨r,c,he,hb⟩ := ih
    obtain ⟨r',c',hs,hl⟩ := payload_count_step_shape r c
    refine ⟨r',c',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

 theorem payload_count_clock_length (clock input : List Bool) :
    ((payloadCountStep^[clock.length]) (pair input [])).length ≤
      2*input.length+2+2*clock.length := by
  obtain ⟨r,c,he,hb⟩ := payload_count_iterate_shape clock.length input []
  rw [he]
  simpa only [pair_length,List.length_nil,Nat.add_zero] using hb

end IV04.Paper.Computational
