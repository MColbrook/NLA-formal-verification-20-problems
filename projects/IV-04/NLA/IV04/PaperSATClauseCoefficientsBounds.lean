module

public import NLA.IV04.PaperSATClauseCoefficientsDefinitions
public import NLA.IV04.PaperSATLiteralMatchPoly
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
 theorem clause_coefficient_pack_length (rest query output : List Bool) :
    (clauseCoefficientPack rest query output).length=2*rest.length+2*query.length+output.length+4 := by
  simp only [clauseCoefficientPack,pair_length];omega
 theorem clause_coefficient_step_pair (rest query output : List Bool) :
    clauseCoefficientStep (clauseCoefficientPack rest query output)=
      if rest=[] then clauseCoefficientPack rest query output else
        clauseCoefficientPack (pairSnd rest) query
          (pair (polynomialLiteralMatchCount (pair (pairFst rest) query)) output) := by
  simp only [clauseCoefficientStep,clauseCoefficientPack,pairFst_pair,pairSnd_pair]
  cases rest <;> simp [nonemptyFlag,caseBit₀,caseBit]
 theorem clause_coefficient_step_shape (rest query output : List Bool) :
    ∃ r o : List Bool, clauseCoefficientStep (clauseCoefficientPack rest query output)=
      clauseCoefficientPack r query o ∧
      24*r.length+o.length ≤ 24*rest.length+output.length+12*query.length+34 := by
  rw [clause_coefficient_step_pair]
  split_ifs
  · exact ⟨rest,output,rfl,by omega⟩
  · refine ⟨_,_,rfl,?_⟩
    have hp := pair_projection_budget rest
    have hc := polynomial_literal_match_count_length (pair (pairFst rest) query)
    simp only [pair_length] at hc ⊢
    omega
 theorem clause_coefficient_iterate_shape (k : ℕ) (rest query output : List Bool) :
    ∃ r o : List Bool, (clauseCoefficientStep^[k]) (clauseCoefficientPack rest query output)=
      clauseCoefficientPack r query o ∧
      24*r.length+o.length ≤ 24*rest.length+output.length+(12*query.length+34)*k := by
  induction k with
  | zero => exact ⟨rest,output,rfl,by simp⟩
  | succ k ih =>
    obtain ⟨r,o,he,hb⟩ := ih
    obtain ⟨r',o',hs,hl⟩ := clause_coefficient_step_shape r query o
    refine ⟨r',o',?_,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · rw [Nat.mul_succ];omega
 theorem clause_coefficient_clock_length (clock input : List Bool) :
    ((clauseCoefficientStep^[clock.length])
      (clauseCoefficientPack (pairFst input) (pairSnd input) [])).length ≤
        24*input.length+4+(12*input.length+34)*clock.length := by
  obtain ⟨r,o,he,hb⟩ := clause_coefficient_iterate_shape clock.length (pairFst input) (pairSnd input) []
  have hp := pair_projection_budget input
  have hq := pairSnd_length_le input
  have hm := Nat.mul_le_mul_right clock.length (show 12*(pairSnd input).length+34 ≤ 12*input.length+34 by omega)
  rw [he,clause_coefficient_pack_length]
  simp only [List.length_nil,Nat.add_zero] at hb
  omega
 theorem polynomial_sat_clause_coefficients_length (input : List Bool) :
    (polynomialSATClauseCoefficients input).length ≤
      24*input.length+4+(12*input.length+34)*input.length := by
  have hs := clause_coefficient_clock_length input input
  have hp := pairSnd_length_le (clauseCoefficientState input)
  have hq := pairSnd_length_le (pairSnd (clauseCoefficientState input))
  unfold polynomialSATClauseCoefficients
  unfold clauseCoefficientState at hp hq ⊢
  omega
end IV04.Paper.Computational
