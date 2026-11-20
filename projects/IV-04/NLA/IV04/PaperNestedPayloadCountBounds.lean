module

public import NLA.IV04.PaperNestedPayloadCountDefinitions
public import NLA.IV04.PaperPayloadCountPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

 theorem nested_payload_count_step_pair (rest total : List Bool) :
    nestedPayloadCountStep (pair rest total)=
      if rest=[] then pair rest total else pair (pairSnd rest)
        (polynomialWordAdd total (polynomialPayloadCount (pairFst rest))) := by
  simp only [nestedPayloadCountStep,pairFst_pair,pairSnd_pair]
  cases rest <;> simp [nonemptyFlag,caseBit₀,caseBit]

 theorem nested_payload_count_step_shape (rest total : List Bool) :
    ∃ r t : List Bool, nestedPayloadCountStep (pair rest total)=pair r t ∧
      4*r.length+t.length ≤ 4*rest.length+total.length+3 := by
  rw [nested_payload_count_step_pair]
  split_ifs
  · exact ⟨rest,total,rfl,by omega⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pair_projection_budget rest
    have hc := polynomial_payload_count_length (pairFst rest)
    have ha := polynomial_word_add_length total (polynomialPayloadCount (pairFst rest))
    omega

 theorem nested_payload_count_iterate_shape (k : ℕ) (rest total : List Bool) :
    ∃ r t : List Bool, (nestedPayloadCountStep^[k]) (pair rest total)=pair r t ∧
      4*r.length+t.length ≤ 4*rest.length+total.length+3*k := by
  induction k with
  | zero => exact ⟨rest,total,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨r,t,he,hb⟩ := ih
    obtain ⟨r',t',hs,hl⟩ := nested_payload_count_step_shape r t
    refine ⟨r',t',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

 theorem nested_payload_count_clock_length (clock input : List Bool) :
    ((nestedPayloadCountStep^[clock.length]) (pair input [])).length ≤
      4*input.length+2+3*clock.length := by
  obtain ⟨r,t,he,hb⟩ := nested_payload_count_iterate_shape clock.length input []
  rw [he]
  simp only [pair_length,List.length_nil] at hb ⊢
  omega

end IV04.Paper.Computational
