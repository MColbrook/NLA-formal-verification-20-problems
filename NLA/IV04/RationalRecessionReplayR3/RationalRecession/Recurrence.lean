module

public import NLA.IV04.RationalRecessionReplayR3.PureDefinitions
/- Actual finite masks recur at arbitrarily large natural thresholds. -/
public import NLA.IV04.PolyhedronSupportReplayR3.OriginalObjectiveAttainment.Attainment

@[expose] public section

set_option autoImplicit false
namespace Reference.IV04RationalRecessionRay
noncomputable section

theorem finite_type_has_unbounded_fiber {α : Type*} [Fintype α] (f : ℕ → α) :
    ∃ a, ∀ K : ℕ, ∃ k, K ≤ k ∧ f k=a := by
  classical
  by_contra hn
  push Not at hn
  choose bound hbound using hn
  let K := (Finset.univ : Finset α).sup bound
  have hle : bound (f K) ≤ K := Finset.le_sup (Finset.mem_univ (f K))
  exact hbound (f K) K hle rfl

#print axioms finite_type_has_unbounded_fiber
end
end Reference.IV04RationalRecessionRay
