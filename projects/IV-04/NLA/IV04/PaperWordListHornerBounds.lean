module

public import NLA.IV04.PaperWordListHornerDefinitions
public import NLA.IV04.PaperCanonicalProduct
public import NLA.IV04.PaperWordListSumBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem word_list_horner_step_pair (rest base total : List Bool) :
    wordListHornerStep (Complexity.pair rest (Complexity.pair base total)) =
      if rest=[] then Complexity.pair rest (Complexity.pair base total) else
        Complexity.pair (Complexity.pairSnd rest) (Complexity.pair base
          (polynomialWordAdd (canonicalWordMultiply total base) (Complexity.pairFst rest))) := by
  simp only [wordListHornerStep, Complexity.pairFst_pair, Complexity.pairSnd_pair]
  cases rest <;> simp [Complexity.nonemptyFlag, Complexity.caseBit, Complexity.caseBit₀]

theorem word_list_horner_step_shape (rest base total : List Bool) :
    ∃ r t : List Bool,
      wordListHornerStep (Complexity.pair rest (Complexity.pair base total)) =
        Complexity.pair r (Complexity.pair base t) ∧
      (Complexity.pair r (Complexity.pair base t)).length ≤
        (Complexity.pair rest (Complexity.pair base total)).length+base.length+1 := by
  rw [word_list_horner_step_pair]
  split_ifs with he
  · exact ⟨rest,total,rfl,by omega⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pair_projection_budget rest
    have hm := canonical_word_multiply_length total base
    have ha := polynomial_word_add_length (canonicalWordMultiply total base) (Complexity.pairFst rest)
    simp only [Complexity.pair_length]
    omega

theorem word_list_horner_iterate_shape (k : ℕ) (rest base total : List Bool) :
    ∃ r t : List Bool,
      (wordListHornerStep^[k]) (Complexity.pair rest (Complexity.pair base total)) =
        Complexity.pair r (Complexity.pair base t) ∧
      (Complexity.pair r (Complexity.pair base t)).length ≤
        (Complexity.pair rest (Complexity.pair base total)).length+k*(base.length+1) := by
  induction k with
  | zero => exact ⟨rest,total,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨r,t,he,hl⟩ := ih
    obtain ⟨r',t',hs,hbound⟩ := word_list_horner_step_shape r base t
    refine ⟨r',t',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · nlinarith only [hl,hbound]

theorem word_list_horner_clock_length (clock input : List Bool) :
    ((wordListHornerStep^[clock.length])
      (Complexity.pair (Complexity.pairSnd input) (Complexity.pair (Complexity.pairFst input) []))).length ≤
        4*input.length+4+clock.length*(input.length+1) := by
  obtain ⟨r,t,he,hl⟩ := word_list_horner_iterate_shape clock.length
    (Complexity.pairSnd input) (Complexity.pairFst input) []
  have hf := Complexity.pairFst_length_le input
  have hs := Complexity.pairSnd_length_le input
  simp only [Complexity.pair_length, List.length_nil] at hl
  rw [he]
  simp only [Complexity.pair_length]
  nlinarith only [hl,hf,hs]

#print axioms word_list_horner_clock_length
end IV04.Paper.Computational
