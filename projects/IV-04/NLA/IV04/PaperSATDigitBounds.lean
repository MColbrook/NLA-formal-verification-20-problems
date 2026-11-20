module

public import NLA.IV04.PaperSATLiteralCounts
public import NLA.IV04.PaperPositionalDigits
public import NLA.IV04.PaperSubsetPartitionDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction
open Complexity.SAT

private theorem selected_digits_le_all (φ : CNF) (selected : SATSlot φ → Bool)
    (j : SATDigit φ) :
    satSelectedDigits φ selected j ≤ ∑ i, satWeightDigits φ i j := by
  apply Finset.sum_le_sum
  intro i _
  cases selected i <;> simp

theorem sat_all_variable_digits (φ : CNF) (v : Fin (satVariables φ)) :
    (∑ i : SATSlot φ, satWeightDigits φ i (Sum.inl v)) = 2 := by
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp [satWeightDigits]

theorem sat_all_clause_digits_bound (φ : CNF) (j : Fin φ.length) :
    (∑ i : SATSlot φ, satWeightDigits φ i (Sum.inr j)) ≤
      2 * satClauseTarget φ + (satClauseTarget φ - 1) := by
  have hcount : ∀ v : Fin (satVariables φ), ∀ b : Bool,
      literalCount (satClause φ j) v.val b ≤ satLiteralBudget φ := by
    intro v b
    exact le_trans (literal_count_le_length _ _ _) (Nat.le_of_lt (sat_clause_length_lt_budget φ j))
  have hvars : (∑ v : Fin (satVariables φ), ∑ b : Bool,
      literalCount (satClause φ j) v.val b) ≤ 2 * satClauseTarget φ := by
    calc
      _ ≤ ∑ _v : Fin (satVariables φ), ∑ _b : Bool, satLiteralBudget φ := by
        apply Finset.sum_le_sum
        intro v _
        exact Finset.sum_le_sum (fun b _ => hcount v b)
      _ = _ := by simp [satClauseTarget]; ring
  have hslack : (∑ q : Fin φ.length, ∑ _k : Fin (satClauseTarget φ - 1),
      if q = j then 1 else 0 : ℕ) = satClauseTarget φ - 1 := by simp
  simp only [satWeightDigits, Fintype.sum_sum_type, Fintype.sum_prod_type]
  rw [hslack]
  exact Nat.add_le_add_right hvars _

theorem sat_selected_digits_carry_free (φ : CNF) (selected : SATSlot φ → Bool) :
    ∀ j, satSelectedDigits φ selected j < satDigitBase φ := by
  intro j
  have hK := sat_clause_target_positive φ
  cases j with
  | inl v =>
    have h := selected_digits_le_all φ selected (Sum.inl v)
    rw [sat_all_variable_digits] at h
    unfold satDigitBase
    omega
  | inr q =>
    have h := le_trans (selected_digits_le_all φ selected (Sum.inr q))
      (sat_all_clause_digits_bound φ q)
    unfold satDigitBase
    omega

theorem sat_target_digits_carry_free (φ : CNF) :
    ∀ j, satTargetDigits φ j < satDigitBase φ := by
  intro j
  cases j <;> simp [satTargetDigits, satDigitBase] <;> omega

theorem sat_digit_value_injective (φ : CNF) (d e : SATDigit φ → ℕ)
    (hd : ∀ j, d j < satDigitBase φ) (he : ∀ j, e j < satDigitBase φ)
    (hv : satDigitValue φ d = satDigitValue φ e) : d = e := by
  have hb : 0 < satDigitBase φ := by unfold satDigitBase; omega
  have h := positional_value_injective (satDigitBase φ) hb _
    (fun k => d (finSumFinEquiv.symm k)) (fun k => e (finSumFinEquiv.symm k))
    (fun k => hd _) (fun k => he _) hv
  funext j
  have hj := congrFun h (finSumFinEquiv j)
  simpa using hj

theorem sat_selected_digit_value (φ : CNF) (selected : SATSlot φ → Bool) :
    (∑ i, if selected i then satSubsetWeights φ i else 0) =
      satDigitValue φ (satSelectedDigits φ selected) := by
  exact positional_selected_value (satDigitBase φ) _
    (fun i k => satWeightDigits φ i (finSumFinEquiv.symm k)) selected

/-- Numeric subset equality is equivalent to every actual variable/clause digit equation. -/
theorem sat_subset_sum_iff_digit_equations (φ : CNF) :
    HasSubsetSum (satSubsetWeights φ) (satSubsetTarget φ) ↔
      ∃ selected : SATSlot φ → Bool, satSelectedDigits φ selected = satTargetDigits φ := by
  constructor
  · rintro ⟨selected, h⟩
    rw [sat_selected_digit_value] at h
    exact ⟨selected, sat_digit_value_injective φ _ _
      (sat_selected_digits_carry_free φ selected) (sat_target_digits_carry_free φ) h⟩
  · rintro ⟨selected, h⟩
    refine ⟨selected, ?_⟩
    rw [sat_selected_digit_value, h]
    rfl

private theorem positional_value_positive_of_digit (b : ℕ) (hb : 0 < b) (n : ℕ)
    (d : Fin n → ℕ) (j : Fin n) (hj : 0 < d j) : 0 < positionalValue b d := by
  exact lt_of_lt_of_le (Nat.mul_pos hj (pow_pos hb _))
    (Finset.single_le_sum (fun i _ => Nat.zero_le (d i * b^i.val)) (Finset.mem_univ j))

theorem sat_subset_weights_positive (φ : CNF) : ∀ i, 0 < satSubsetWeights φ i := by
  intro i
  have hb : 0 < satDigitBase φ := by unfold satDigitBase; omega
  cases i with
  | inl p =>
    rcases p with ⟨v,b⟩
    apply positional_value_positive_of_digit _ hb _ _ (finSumFinEquiv (Sum.inl v))
    simp [satWeightDigits]
  | inr p =>
    rcases p with ⟨j,k⟩
    apply positional_value_positive_of_digit _ hb _ _ (finSumFinEquiv (Sum.inr j))
    simp [satWeightDigits]

#print axioms sat_selected_digits_carry_free
#print axioms sat_target_digits_carry_free
#print axioms sat_subset_sum_iff_digit_equations
#print axioms sat_subset_weights_positive
end IV04.Paper.Computational.SATReduction