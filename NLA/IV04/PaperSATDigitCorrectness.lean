module

public import NLA.IV04.PaperSATDigitSelection
public import NLA.IV04.PaperSubsetPartition
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace IV04.Paper.Computational.SATReduction
open Complexity.SAT

private theorem bounded_slack_exists (n r : ℕ) (hr : r ≤ n) :
    ∃ q : Fin n → Bool, (∑ k, if q k then 1 else 0 : ℕ) = r := by
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq (s := Finset.univ (α := Fin n))
    (by simpa using hr)
  refine ⟨fun k => decide (k ∈ s), ?_⟩
  simpa using hcard

private theorem selected_polarity_count (φ : CNF) (selected : SATSlot φ → Bool)
    (hchoice : ∀ v : Fin (satVariables φ),
      (if selected (Sum.inl (v,false)) then 1 else 0 : ℕ) +
      (if selected (Sum.inl (v,true)) then 1 else 0) = 1)
    (j : Fin φ.length) :
    (∑ v : Fin (satVariables φ), ∑ b : Bool,
      if selected (Sum.inl (v,b)) then literalCount (satClause φ j) v.val b else 0) =
    trueLiteralCount (satClause φ j)
      (Assignment.get (List.ofFn (fun v : Fin (satVariables φ) => selected (Sum.inl (v,true))))) := by
  have hp : ∀ v : Fin (satVariables φ),
      (∑ b : Bool, if selected (Sum.inl (v,b)) then literalCount (satClause φ j) v.val b else 0) =
      literalCount (satClause φ j) v.val (selected (Sum.inl (v,true))) := by
    intro v
    have hv := hchoice v
    simp only [Fintype.sum_bool]
    cases hf : selected (Sum.inl (v,false)) <;>
      cases ht : selected (Sum.inl (v,true)) <;> simp [hf, ht] at hv ⊢
  simp_rw [hp]
  let a : Fin (satVariables φ) → Bool := fun v => selected (Sum.inl (v,true))
  have h := sum_variable_literal_count (satVariables φ) (satClause φ j)
    (fun ℓ hℓ => sat_literal_variable_lt φ j ℓ hℓ) a
  have hfun : (fun k => if hk : k < satVariables φ then a ⟨k,hk⟩ else false) =
      Assignment.get (List.ofFn a) := by
    funext k
    exact (assignment_get_of_fn _ a k).symm
  rw [hfun] at h
  exact h

private theorem assignment_polarity_count (φ : CNF) (a : Fin (satVariables φ) → Bool)
    (j : Fin φ.length) :
    (∑ v : Fin (satVariables φ), ∑ b : Bool,
      if decide (b = a v) then literalCount (satClause φ j) v.val b else 0) =
      trueLiteralCount (satClause φ j) (Assignment.get (List.ofFn a)) := by
  have hp : ∀ v : Fin (satVariables φ),
      (∑ b : Bool, if decide (b = a v) then literalCount (satClause φ j) v.val b else 0) =
      literalCount (satClause φ j) v.val (a v) := by
    intro v
    cases a v <;> simp [Fintype.sum_bool]
  simp_rw [hp]
  simpa only [← assignment_get_of_fn] using
    sum_variable_literal_count (satVariables φ) (satClause φ j)
      (fun ℓ hℓ => sat_literal_variable_lt φ j ℓ hℓ) a

/-- The actual SAT digit equations encode exactly satisfiability, including empty clauses. -/
theorem sat_satisfiable_iff_digit_equations (φ : CNF) :
    φ.Satisfiable ↔ ∃ selected : SATSlot φ → Bool,
      satSelectedDigits φ selected = satTargetDigits φ := by
  rw [sat_satisfiable_iff_bounded_assignment]
  constructor
  · rintro ⟨a, ha⟩
    have hclauses : ∀ j : Fin φ.length,
        Clause.eval (List.ofFn a) (satClause φ j) = true := by
      intro j
      exact List.all_eq_true.mp ha _ (List.getElem_mem j.isLt)
    have hcounts : ∀ j : Fin φ.length,
        0 < trueLiteralCount (satClause φ j) (Assignment.get (List.ofFn a)) ∧
        trueLiteralCount (satClause φ j) (Assignment.get (List.ofFn a)) ≤ satClauseTarget φ := by
      intro j
      refine ⟨(true_literal_count_positive_iff_eval _ _).mpr (hclauses j), ?_⟩
      have hv := sat_variables_positive φ
      have hc := sat_clause_length_lt_budget φ j
      have hcount := true_literal_count_le_length (satClause φ j) (Assignment.get (List.ofFn a))
      have hbudget : satLiteralBudget φ ≤ satClauseTarget φ := by
        unfold satClauseTarget
        calc
          satLiteralBudget φ = 1 * satLiteralBudget φ := by simp
          _ ≤ satVariables φ * satLiteralBudget φ := Nat.mul_le_mul_right _ (by omega)
      omega
    have hslacks : ∀ j : Fin φ.length, ∃ q : Fin (satClauseTarget φ-1) → Bool,
        (∑ k, if q k then 1 else 0 : ℕ) =
          satClauseTarget φ - trueLiteralCount (satClause φ j) (Assignment.get (List.ofFn a)) := by
      intro j
      apply bounded_slack_exists
      have h := hcounts j
      omega
    choose q hq using hslacks
    let selected : SATSlot φ → Bool := Sum.elim
      (fun p => decide (p.2 = a p.1)) (fun p => q p.1 p.2)
    refine ⟨selected, ?_⟩
    funext d
    cases d with
    | inl v =>
      rw [sat_selected_variable_digit]
      change (if decide (false = a v) then 1 else 0 : ℕ) +
        (if decide (true = a v) then 1 else 0) = 1
      cases a v <;> simp
    | inr j =>
      rw [sat_selected_clause_digit]
      change (∑ v : Fin (satVariables φ), ∑ b : Bool,
        if decide (b = a v) then literalCount (satClause φ j) v.val b else 0) +
        (∑ k, if q j k then 1 else 0 : ℕ) = satClauseTarget φ
      rw [assignment_polarity_count, hq j]
      have h := (hcounts j).2
      omega
  · rintro ⟨selected, hd⟩
    let a : Fin (satVariables φ) → Bool := fun v => selected (Sum.inl (v,true))
    have hchoice : ∀ v : Fin (satVariables φ),
        (if selected (Sum.inl (v,false)) then 1 else 0 : ℕ) +
        (if selected (Sum.inl (v,true)) then 1 else 0) = 1 := by
      intro v
      have h := congrFun hd (Sum.inl v)
      simpa only [sat_selected_variable_digit, satTargetDigits] using h
    have hclauses : ∀ j : Fin φ.length,
        Clause.eval (List.ofFn a) (satClause φ j) = true := by
      intro j
      apply (true_literal_count_positive_iff_eval _ _).mp
      have h := congrFun hd (Sum.inr j)
      rw [sat_selected_clause_digit, selected_polarity_count φ selected hchoice j] at h
      change trueLiteralCount (satClause φ j) (Assignment.get (List.ofFn a)) +
        (∑ k, if selected (Sum.inr (j,k)) then 1 else 0 : ℕ) = satClauseTarget φ at h
      have hs := sat_slack_count_bound φ selected j
      have hK := sat_clause_target_positive φ
      omega
    refine ⟨a, List.all_eq_true.mpr ?_⟩
    intro c hc
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hc
    simpa [satClause] using hclauses ⟨k,hk⟩

theorem sat_satisfiable_iff_actual_subset_sum (φ : CNF) :
    φ.Satisfiable ↔ HasSubsetSum (satSubsetWeights φ) (satSubsetTarget φ) := by
  rw [sat_subset_sum_iff_digit_equations]
  exact sat_satisfiable_iff_digit_equations φ

theorem sat_satisfiable_iff_positive_partition (φ : CNF) :
    φ.Satisfiable ↔ SignedPartition
      (subsetPartitionWeights (satSubsetWeights φ) (satSubsetTarget φ)) := by
  rw [subset_partition_iff]
  exact sat_satisfiable_iff_actual_subset_sum φ

theorem sat_partition_all_weights_positive (φ : CNF) :
    ∀ i, 0 < subsetPartitionWeights (satSubsetWeights φ) (satSubsetTarget φ) i :=
  subset_partition_weights_positive _ _ (sat_subset_weights_positive φ)

#print axioms sat_satisfiable_iff_digit_equations
#print axioms sat_satisfiable_iff_actual_subset_sum
#print axioms sat_satisfiable_iff_positive_partition
#print axioms sat_partition_all_weights_positive
end IV04.Paper.Computational.SATReduction