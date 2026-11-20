module

public import NLA.IV04.PaperSATLiteralMatchDefinitions
public import NLA.IV04.PaperPayloadCountBounds
public import NLA.IV04.PaperSignedWordBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

 theorem literal_match_pack_length (rest count query : List Bool) :
    (literalMatchPack rest count query).length=2*rest.length+2*count.length+query.length+4 := by
  simp only [literalMatchPack,pair_length]
  omega

 theorem literal_match_step_pair (rest count query : List Bool) :
    literalMatchStep (literalMatchPack rest count query)=
      if rest=[] then literalMatchPack rest count query else
        literalMatchPack (pairSnd rest)
          (caseBit₀ (literalMatchFlag (pairFst rest) query) (polynomialWordAdd count [true]) count) query := by
  simp only [literalMatchStep,literalMatchPack,pairFst_pair,pairSnd_pair]
  cases rest <;> simp [nonemptyFlag,caseBit₀,caseBit]

 theorem literal_match_step_shape (rest count query : List Bool) :
    ∃ r c : List Bool, literalMatchStep (literalMatchPack rest count query)=literalMatchPack r c query ∧
      (literalMatchPack r c query).length ≤ (literalMatchPack rest count query).length+4 := by
  rw [literal_match_step_pair]
  split_ifs
  · exact ⟨rest,count,rfl,by omega⟩
  · refine ⟨_,_,rfl,?_⟩
    have hr := pairSnd_length_le rest
    have ha := polynomial_word_add_length count [true]
    have hc := case_bit_zero_property (P:=fun bits => bits.length ≤ count.length+2)
      (literalMatchFlag (pairFst rest) query) (polynomialWordAdd count [true]) count
      (by simpa using ha.le) (by omega)
    simp only [literal_match_pack_length,List.length_cons,List.length_nil] at ha ⊢
    omega

 theorem literal_match_iterate_shape (k : ℕ) (rest count query : List Bool) :
    ∃ r c : List Bool, (literalMatchStep^[k]) (literalMatchPack rest count query)=literalMatchPack r c query ∧
      (literalMatchPack r c query).length ≤ (literalMatchPack rest count query).length+4*k := by
  induction k with
  | zero => exact ⟨rest,count,rfl,le_refl _⟩
  | succ k ih =>
    obtain ⟨r,c,he,hb⟩ := ih
    obtain ⟨r',c',hs,hl⟩ := literal_match_step_shape r c query
    refine ⟨r',c',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

 theorem literal_match_clock_length (clock input : List Bool) :
    ((literalMatchStep^[clock.length]) (literalMatchPack (pairFst input) [] (pairSnd input))).length ≤
      2*input.length+4+4*clock.length := by
  obtain ⟨r,c,he,hb⟩ := literal_match_iterate_shape clock.length (pairFst input) [] (pairSnd input)
  have hp := pair_projection_budget input
  rw [he]
  simp only [literal_match_pack_length,List.length_nil] at hb ⊢
  omega

end IV04.Paper.Computational
