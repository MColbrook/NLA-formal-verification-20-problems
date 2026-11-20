module

public import NLA.IV04.PaperSATDigitDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction
open Complexity.SAT

theorem sat_variables_positive (φ : CNF) : 0 < satVariables φ := by
  unfold satVariables; omega

theorem sat_literal_budget_positive (φ : CNF) : 0 < satLiteralBudget φ := by
  unfold satLiteralBudget; omega

theorem sat_clause_target_positive (φ : CNF) : 0 < satClauseTarget φ :=
  Nat.mul_pos (sat_variables_positive φ) (sat_literal_budget_positive φ)

theorem literal_count_le_length (c : Clause) (v : ℕ) (b : Bool) :
    literalCount c v b ≤ c.length := by
  induction c with
  | nil => simp [literalCount]
  | cons ℓ c ih =>
    simp only [literalCount, List.map_cons, List.sum_cons, List.length_cons] at *
    split <;> omega

theorem true_literal_count_le_length (c : Clause) (a : ℕ → Bool) :
    trueLiteralCount c a ≤ c.length := by
  induction c with
  | nil => simp [trueLiteralCount]
  | cons ℓ c ih =>
    simp only [trueLiteralCount, List.map_cons, List.sum_cons, List.length_cons] at *
    split <;> omega

theorem true_literal_count_positive_iff (c : Clause) (a : ℕ → Bool) :
    0 < trueLiteralCount c a ↔ ∃ ℓ ∈ c, a ℓ.var = ℓ.sign := by
  induction c with
  | nil => simp [trueLiteralCount]
  | cons ℓ c ih =>
    simp only [trueLiteralCount, List.map_cons, List.sum_cons]
    by_cases h : a ℓ.var = ℓ.sign
    · simp [h]
    · simpa [h, trueLiteralCount] using ih

theorem clause_length_le_flatten {φ : CNF} {c : Clause} (hc : c ∈ φ) :
    c.length ≤ φ.flatten.length := by
  induction φ with
  | nil => simp at hc
  | cons d φ ih =>
    simp only [List.mem_cons] at hc
    simp only [List.flatten_cons, List.length_append]
    rcases hc with h | h
    · subst c; omega
    · have hi := ih h; omega

theorem sat_clause_length_lt_budget (φ : CNF) (j : Fin φ.length) :
    (satClause φ j).length < satLiteralBudget φ := by
  have hc : satClause φ j ∈ φ := List.getElem_mem j.isLt
  have h := clause_length_le_flatten hc
  unfold satLiteralBudget
  omega

theorem sat_literal_variable_lt (φ : CNF) (j : Fin φ.length)
    (ℓ : Lit) (hℓ : ℓ ∈ satClause φ j) : ℓ.var < satVariables φ := by
  have hc : satClause φ j ∈ φ := List.getElem_mem j.isLt
  have h := le_trans (Clause.var_le_maxVar hℓ) (CNF.clause_maxVar_le_maxVar hc)
  unfold satVariables
  omega

private theorem single_variable_count (V : ℕ) (ℓ : Lit) (hℓ : ℓ.var < V)
    (a : Fin V → Bool) :
    (∑ v : Fin V, if ℓ.var = v.val ∧ ℓ.sign = a v then 1 else 0 : ℕ) =
      if a ⟨ℓ.var,hℓ⟩ = ℓ.sign then 1 else 0 := by
  let v : Fin V := ⟨ℓ.var,hℓ⟩
  rw [Finset.sum_eq_single v]
  · simp [v, eq_comm]
  · intro j _ hj
    have hne : ℓ.var ≠ j.val := by
      intro heq
      apply hj
      exact Fin.ext heq.symm
    simp [hne]
  · simp

/-- Counting the selected variable polarity counts exactly the true literal occurrences. -/
theorem sum_variable_literal_count (V : ℕ) (c : Clause)
    (hc : ∀ ℓ ∈ c, ℓ.var < V) (a : Fin V → Bool) :
    (∑ v : Fin V, literalCount c v.val (a v)) =
      trueLiteralCount c (fun k => if hk : k < V then a ⟨k,hk⟩ else false) := by
  induction c with
  | nil => simp [literalCount, trueLiteralCount]
  | cons ℓ c ih =>
    have hℓ := hc ℓ (by simp)
    have ht : ∀ l ∈ c, l.var < V := fun l hl => hc l (by simp [hl])
    simp only [literalCount, List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib]
    rw [single_variable_count V ℓ hℓ a]
    have hi := ih ht
    change (if a ⟨ℓ.var,hℓ⟩ = ℓ.sign then 1 else 0) +
      (∑ v : Fin V, literalCount c v.val (a v)) = _
    rw [hi]
    simp [trueLiteralCount, hℓ]

#print axioms literal_count_le_length
#print axioms true_literal_count_positive_iff
#print axioms sum_variable_literal_count
end IV04.Paper.Computational.SATReduction