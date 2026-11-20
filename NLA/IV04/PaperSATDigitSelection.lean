module

public import NLA.IV04.PaperSATDigitBounds
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction
open Complexity.SAT

/-- The actual list assignment has its specified values inside and outside Fin V. -/
theorem assignment_get_of_fn (V : ℕ) (a : Fin V → Bool) (k : ℕ) :
    Assignment.get (List.ofFn a) k = if hk : k < V then a ⟨k,hk⟩ else false := by
  by_cases hk : k < V
  · have hl : k < (List.ofFn a).length := by simpa using hk
    simp only [dif_pos hk, Assignment.get, List.getElem?_eq_getElem hl,
      List.getElem_ofFn, Option.getD_some]
  · simp only [dif_neg hk, Assignment.get]
    rw [List.getElem?_eq_none (by simp; omega)]
    rfl

theorem true_literal_count_positive_iff_eval (c : Clause) (α : Assignment) :
    0 < trueLiteralCount c α.get ↔ Clause.eval α c = true := by
  rw [true_literal_count_positive_iff]
  simp [Clause.eval, Lit.eval, List.any_eq_true]

/-- Bounded Fin assignments and the paper's actual SAT assignment semantics agree. -/
theorem sat_satisfiable_iff_bounded_assignment (φ : CNF) :
    φ.Satisfiable ↔ ∃ a : Fin (satVariables φ) → Bool,
      CNF.eval (List.ofFn a) φ = true := by
  constructor
  · rintro ⟨α,hα⟩
    let a : Fin (satVariables φ) → Bool := fun i => α.get i.val
    refine ⟨a, ?_⟩
    have htake := CNF.eval_take α φ (satVariables φ) (by simp [satVariables])
    rw [← htake] at hα
    rw [CNF.eval_eq_of_agree _ (α.take (satVariables φ)) φ]
    · exact hα
    · intro k
      rw [assignment_get_of_fn]
      by_cases hk : k < satVariables φ
      · rw [dif_pos hk, Assignment.get_take α k _ hk]
      · rw [dif_neg hk]
        simp only [Assignment.get]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
  · rintro ⟨a,ha⟩
    exact ⟨List.ofFn a,ha⟩

theorem sat_selected_variable_digit (φ : CNF) (selected : SATSlot φ → Bool)
    (v : Fin (satVariables φ)) :
    satSelectedDigits φ selected (Sum.inl v) =
      (if selected (Sum.inl (v,false)) then 1 else 0) +
      (if selected (Sum.inl (v,true)) then 1 else 0) := by
  unfold satSelectedDigits
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hterm : ∀ u : Fin (satVariables φ), ∀ b : Bool,
      (if selected (Sum.inl (u,b)) then satWeightDigits φ (Sum.inl (u,b)) (Sum.inl v) else 0) =
      if u = v then (if selected (Sum.inl (u,b)) then 1 else 0) else 0 := by
    intro u b
    by_cases h : u = v <;> simp [satWeightDigits, h]
  simp_rw [hterm]
  simp only [Fintype.sum_bool]
  simp [satWeightDigits, Finset.sum_add_distrib, add_comm]

theorem sat_selected_clause_digit (φ : CNF) (selected : SATSlot φ → Bool)
    (j : Fin φ.length) :
    satSelectedDigits φ selected (Sum.inr j) =
      (∑ v : Fin (satVariables φ), ∑ b : Bool,
        if selected (Sum.inl (v,b)) then literalCount (satClause φ j) v.val b else 0) +
      (∑ k : Fin (satClauseTarget φ-1), if selected (Sum.inr (j,k)) then 1 else 0) := by
  unfold satSelectedDigits
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hterm : ∀ q : Fin φ.length, ∀ k : Fin (satClauseTarget φ-1),
      (if selected (Sum.inr (q,k)) then satWeightDigits φ (Sum.inr (q,k)) (Sum.inr j) else 0) =
      if q = j then (if selected (Sum.inr (q,k)) then 1 else 0) else 0 := by
    intro q k
    by_cases h : q = j <;> simp [satWeightDigits, h]
  simp_rw [hterm]
  simp [satWeightDigits]

theorem sat_slack_count_bound (φ : CNF) (selected : SATSlot φ → Bool)
    (j : Fin φ.length) :
    (∑ k : Fin (satClauseTarget φ-1), if selected (Sum.inr (j,k)) then 1 else 0 : ℕ) ≤
      satClauseTarget φ-1 := by
  calc
    _ ≤ ∑ _k : Fin (satClauseTarget φ-1), (1 : ℕ) := by
      exact Finset.sum_le_sum (fun k _ => by cases selected (Sum.inr (j,k)) <;> simp)
    _ = _ := by simp

#print axioms sat_satisfiable_iff_bounded_assignment
#print axioms sat_selected_variable_digit
#print axioms sat_selected_clause_digit
end IV04.Paper.Computational.SATReduction