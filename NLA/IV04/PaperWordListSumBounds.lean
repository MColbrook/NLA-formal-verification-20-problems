module

public import NLA.IV04.PaperWordListSumDefinitions
public import NLA.IV04.PaperWordListProductBounds
public import NLA.IV04.PaperWordAdderPoly
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem word_list_sum_step_pair (rest total : List Bool) :
    wordListSumStep (Complexity.pair rest total)=
      if rest=[] then Complexity.pair rest total else
        Complexity.pair (Complexity.pairSnd rest) (polynomialWordAdd total (Complexity.pairFst rest)) := by
  simp only [wordListSumStep,Complexity.pairFst_pair,Complexity.pairSnd_pair]
  cases rest <;> simp [Complexity.nonemptyFlag,Complexity.caseBit,Complexity.caseBit₀]

theorem word_list_sum_step_shape (rest total : List Bool) :
    ∃ r t : List Bool, wordListSumStep (Complexity.pair rest total)=Complexity.pair r t ∧
      (Complexity.pair r t).length ≤ (Complexity.pair rest total).length+1 := by
  rw [word_list_sum_step_pair]
  split_ifs with he
  · exact ⟨rest,total,rfl,Nat.le_succ _⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pair_projection_budget rest
    have ha := polynomial_word_add_length total (Complexity.pairFst rest)
    simp only [Complexity.pair_length]
    omega

theorem word_list_sum_iterate_shape (k : ℕ) (rest total : List Bool) :
    ∃ r t : List Bool, (wordListSumStep^[k]) (Complexity.pair rest total)=Complexity.pair r t ∧
      (Complexity.pair r t).length ≤ (Complexity.pair rest total).length+k := by
  induction k with
  | zero => exact ⟨rest,total,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨r,t,he,hl⟩ := ih
    obtain ⟨r',t',hs,hbound⟩ := word_list_sum_step_shape r t
    refine ⟨r',t',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

theorem word_list_sum_iterate_length (k : ℕ) (rest total : List Bool) :
    ((wordListSumStep^[k]) (Complexity.pair rest total)).length ≤
      2*rest.length+total.length+2+k := by
  obtain ⟨r,t,he,hl⟩ := word_list_sum_iterate_shape k rest total
  rw [he]
  simp only [Complexity.pair_length] at hl ⊢
  omega

#print axioms word_list_sum_iterate_length
end IV04.Paper.Computational
