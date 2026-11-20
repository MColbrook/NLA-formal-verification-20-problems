module

public import NLA.IV04.PaperBudgetedPowerDefinitions
public import NLA.IV04.PaperCanonicalProduct
public import NLA.IV04.PaperCountedMachineStep
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open Complexity
namespace IV04.Paper.Computational

theorem budgeted_power_step_pair (count base product : List Bool) :
    budgetedPowerStep (pair count (pair base product))=
      if count=[] then pair count (pair base product) else
        pair (decrementCount count) (pair base (canonicalWordMultiply product base)) := by
  simp only [budgetedPowerStep,pairFst_pair,pairSnd_pair]
  cases count <;> simp [nonemptyFlag,caseBit,caseBit₀]

theorem budgeted_power_step_shape (count base product : List Bool) :
    ∃ c p : List Bool, budgetedPowerStep (pair count (pair base product))=pair c (pair base p) ∧
      c.length ≤ count.length ∧ p.length ≤ product.length+base.length := by
  rw [budgeted_power_step_pair]
  split_ifs
  · exact ⟨count,product,rfl,le_refl _,by omega⟩
  · exact ⟨_,_,rfl,decrement_count_length count,canonical_word_multiply_length product base⟩

theorem budgeted_power_iterate_shape (k : ℕ) (count base product : List Bool) :
    ∃ c p : List Bool, (budgetedPowerStep^[k]) (pair count (pair base product))=pair c (pair base p) ∧
      c.length ≤ count.length ∧ p.length ≤ product.length+k*base.length := by
  induction k with
  | zero => exact ⟨count,product,rfl,le_refl _,by omega⟩
  | succ k ih =>
    obtain ⟨c,p,he,hc,hp⟩ := ih
    obtain ⟨c',p',hs,hc',hp'⟩ := budgeted_power_step_shape c base p
    refine ⟨c',p',?_,hc'.trans hc,?_⟩
    · rw [Function.iterate_succ_apply',he,hs]
    · simp only [Nat.succ_mul]; omega

theorem budgeted_power_iterate_length (k : ℕ) (count base product : List Bool) :
    ((budgetedPowerStep^[k]) (pair count (pair base product))).length ≤
      2*count.length+2*base.length+product.length+4+k*base.length := by
  obtain ⟨c,p,he,hc,hp⟩ := budgeted_power_iterate_shape k count base product
  rw [he]
  simp only [pair_length]
  omega

theorem budgeted_power_clock_length (clock input : List Bool) :
    ((budgetedPowerStep^[clock.length])
      (pair (canonicalWord (pairFst input)) (pair (pairFst (pairSnd input)) [true]))).length ≤
      4*input.length+5+clock.length*input.length := by
  have h := budgeted_power_iterate_length clock.length (canonicalWord (pairFst input))
    (pairFst (pairSnd input)) [true]
  have hc := (canonical_word_length (pairFst input)).trans (pairFst_length_le input)
  have hb := (pairFst_length_le (pairSnd input)).trans (pairSnd_length_le input)
  have hm := Nat.mul_le_mul_left clock.length hb
  simp only [List.length_cons,List.length_nil] at h
  omega

theorem budgeted_power_state_length (input : List Bool) :
    (budgetedPowerState input).length ≤ 4*input.length+5+input.length*input.length :=
  budgeted_power_clock_length input input

#print axioms budgeted_power_state_length
end IV04.Paper.Computational
