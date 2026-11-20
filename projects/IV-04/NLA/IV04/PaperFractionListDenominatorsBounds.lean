module

public import NLA.IV04.PaperFractionListDenominatorsDefinitions
public import NLA.IV04.PaperWordListProductBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

theorem fraction_list_denominators_step_pair (rest output : List Bool) :
    fractionListDenominatorsStep (Complexity.pair rest output)=
      if rest=[] then Complexity.pair rest output else Complexity.pair (Complexity.pairSnd rest)
        (Complexity.pair (Complexity.pairSnd (Complexity.pairFst rest)) output) := by
  simp only [fractionListDenominatorsStep,Complexity.pairFst_pair,Complexity.pairSnd_pair]
  cases rest <;> simp [Complexity.nonemptyFlag,Complexity.caseBit,Complexity.caseBit₀]

theorem fraction_list_denominators_step_shape (rest output : List Bool) :
    ∃ r o : List Bool, fractionListDenominatorsStep (Complexity.pair rest output)=Complexity.pair r o ∧
      (Complexity.pair r o).length ≤ (Complexity.pair rest output).length+2 := by
  rw [fraction_list_denominators_step_pair]
  split_ifs with he
  · exact ⟨rest,output,rfl,by omega⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pair_projection_budget rest
    have hd := Complexity.pairSnd_length_le (Complexity.pairFst rest)
    simp only [Complexity.pair_length]
    omega

theorem fraction_list_denominators_iterate_shape (k : ℕ) (rest output : List Bool) :
    ∃ r o : List Bool, (fractionListDenominatorsStep^[k]) (Complexity.pair rest output)=Complexity.pair r o ∧
      (Complexity.pair r o).length ≤ (Complexity.pair rest output).length+2*k := by
  induction k with
  | zero => exact ⟨rest,output,rfl,by omega⟩
  | succ k ih =>
    obtain ⟨r,o,he,hl⟩ := ih
    obtain ⟨r',o',hs,hbound⟩ := fraction_list_denominators_step_shape r o
    refine ⟨r',o',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · omega

theorem fraction_list_denominators_iterate_length (k : ℕ) (rest output : List Bool) :
    ((fractionListDenominatorsStep^[k]) (Complexity.pair rest output)).length ≤
      2*rest.length+output.length+2+2*k := by
  obtain ⟨r,o,he,hl⟩ := fraction_list_denominators_iterate_shape k rest output
  rw [he]
  simp only [Complexity.pair_length] at hl ⊢
  omega

theorem fraction_list_denominators_output_length (input : List Bool) :
    (polynomialFractionListDenominators input).length ≤ 4*input.length+2 := by
  have h := fraction_list_denominators_iterate_length input.length input []
  have hs := Complexity.pairSnd_length_le (fractionListDenominatorsState input)
  simp only [List.length_nil] at h
  have hstate : (fractionListDenominatorsState input).length ≤ 4*input.length+2 := by
    change ((fractionListDenominatorsStep^[input.length]) (Complexity.pair input [])).length ≤ _
    omega
  exact hs.trans hstate

#print axioms fraction_list_denominators_output_length
end IV04.Paper.Computational
