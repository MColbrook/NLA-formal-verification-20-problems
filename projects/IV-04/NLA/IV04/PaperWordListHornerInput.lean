module

public import NLA.IV04.PaperWordListHornerInputDefinitions
public import NLA.IV04.PaperWordListHornerSemantics
public import NLA.IV04.PaperPositionalDigits
public import NLA.IV04.PaperEncoding
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational
open SATReduction

private theorem horner_word_bits_value (n : ℕ) : wordValue n.bits=n := by
  rw [word_value_foldr]
  exact IV04.Paper.bits_foldr n

theorem positional_value_eq_foldr (b n : ℕ) (d : Fin n → ℕ) :
    positionalValue b d = (List.ofFn d).foldr (fun coefficient value => coefficient+b*value) 0 := by
  induction n with
  | zero => simp [positionalValue,List.ofFn_zero]
  | succ n ih =>
    rw [positional_value_succ,List.ofFn_succ,List.foldr_cons,← ih]

theorem polynomial_word_list_horner_positional_value (b n : ℕ) (d : Fin n → ℕ) :
    wordValue (polynomialWordListHorner (encodedPositionalDigits b n d))=positionalValue b d := by
  have h := polynomial_word_list_horner_value (positionalDigitPayloads d) b.bits
  rw [positional_value_eq_foldr]
  simpa only [encodedPositionalDigits,positionalDigitPayloads,List.foldl_map,
    horner_word_bits_value,List.foldl_reverse,Nat.add_comm,Nat.mul_comm] using h

theorem word_list_horner_positional_actual_polytime : polynomialWordListHorner ∈ Complexity.FP ∧
    ∀ (b n : ℕ) (d : Fin n → ℕ),
      wordValue (polynomialWordListHorner (encodedPositionalDigits b n d))=positionalValue b d :=
  ⟨polynomial_word_list_horner_mem_fp,polynomial_word_list_horner_positional_value⟩

theorem actual_sat_weight_horner_word_value (φ : Complexity.SAT.CNF) (i : SATSlot φ) :
    wordValue (polynomialWordListHorner (actualSATWeightHornerInput φ i))=satSubsetWeights φ i := by
  exact polynomial_word_list_horner_positional_value _ _ _

theorem actual_sat_target_horner_word_value (φ : Complexity.SAT.CNF) :
    wordValue (polynomialWordListHorner (actualSATTargetHornerInput φ))=satSubsetTarget φ := by
  exact polynomial_word_list_horner_positional_value _ _ _

#print axioms word_list_horner_positional_actual_polytime
#print axioms actual_sat_weight_horner_word_value
#print axioms actual_sat_target_horner_word_value
end IV04.Paper.Computational