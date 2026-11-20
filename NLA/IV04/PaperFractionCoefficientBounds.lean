module

public import NLA.IV04.PaperFractionCoefficientStep
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem fraction_coefficient_step_pack (rest prior output : List Bool) :
    fractionCoefficientStep (coefficientPack rest prior output)=
      if rest=[] then coefficientPack rest prior output else
        coefficientPack (pairSnd rest) (canonicalWordMultiply prior (pairSnd (pairFst rest)))
          (pair (clearedFractionWord prior (pairFst rest) (pairSnd rest)) output) := by
  simp only [fractionCoefficientStep,coefficientRest,coefficientPrefix,coefficientOutput,coefficientPack,
    pairFst_pair,pairSnd_pair]
  cases rest <;> simp [nonemptyFlag,caseBit,caseBit₀]

theorem fraction_coefficient_step_shape (rest prior output : List Bool) :
    ∃ r p o : List Bool, fractionCoefficientStep (coefficientPack rest prior output)=coefficientPack r p o ∧
      r.length+p.length ≤ rest.length+prior.length ∧
      o.length ≤ output.length+18*(rest.length+prior.length)+18 := by
  rw [fraction_coefficient_step_pack]
  split_ifs with he
  · exact ⟨rest,prior,output,rfl,le_refl _,by omega⟩
  · refine ⟨_,_,_,rfl,?_,?_⟩
    · have hp := pair_projection_budget rest
      have hd := pairSnd_length_le (pairFst rest)
      have hm := canonical_word_multiply_length prior (pairSnd (pairFst rest))
      omega
    · have hp := pair_projection_budget rest
      have hc := cleared_fraction_word_length prior (pairFst rest) (pairSnd rest)
      simp only [pair_length]
      omega

theorem fraction_coefficient_iterate_shape (k : ℕ) (rest prior output : List Bool) :
    ∃ r p o : List Bool, (fractionCoefficientStep^[k]) (coefficientPack rest prior output)=coefficientPack r p o ∧
      r.length+p.length ≤ rest.length+prior.length ∧
      o.length ≤ output.length+k*(18*(rest.length+prior.length)+18) := by
  induction k with
  | zero => exact ⟨rest,prior,output,rfl,le_refl _,by omega⟩
  | succ k ih =>
    obtain ⟨r,p,o,he,hjoint,hout⟩ := ih
    obtain ⟨r',p',o',hs,hjoint',hout'⟩ := fraction_coefficient_step_shape r p o
    refine ⟨r',p',o',?_,hjoint'.trans hjoint,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · have h18 := Nat.mul_le_mul_left 18 hjoint
      nlinarith

theorem fraction_coefficient_iterate_length (k : ℕ) (rest prior output : List Bool) :
    ((fractionCoefficientStep^[k]) (coefficientPack rest prior output)).length ≤
      2*(rest.length+prior.length)+output.length+4+k*(18*(rest.length+prior.length)+18) := by
  obtain ⟨r,p,o,he,hjoint,hout⟩ := fraction_coefficient_iterate_shape k rest prior output
  rw [he]
  simp only [coefficientPack,pair_length]
  omega

theorem fraction_coefficient_initial_iterate_length (k : ℕ) (input : List Bool) :
    ((fractionCoefficientStep^[k]) (fractionCoefficientInitial input)).length ≤
      2*input.length+6+k*(18*input.length+36) := by
  have h := fraction_coefficient_iterate_length k input [true] []
  simp only [List.length_cons,List.length_nil] at h
  change ((fractionCoefficientStep^[k]) (coefficientPack input [true] [])).length ≤ _
  nlinarith [h]

theorem fraction_coefficient_state_length (input : List Bool) :
    (fractionCoefficientState input).length ≤ 2*input.length+6+input.length*(18*input.length+36) :=
  fraction_coefficient_initial_iterate_length input.length input

#print axioms fraction_coefficient_state_length
end IV04.Paper.Computational
