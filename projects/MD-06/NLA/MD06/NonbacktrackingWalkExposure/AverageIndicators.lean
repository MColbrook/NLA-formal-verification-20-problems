module

public import NLA.MD06.NonbacktrackingWalkExposure.ProbabilityBasic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.MD06WalkExposure
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem actual_finite_average_indicator_bound {α : Type*} [DecidableEq α]
    (S : Finset α) (hp : 0<S.card) (f : α → ℝ) (H : α → Prop) [DecidablePred H] (A B : ℝ)
    (h : ∀ a∈S,f a≤A+(if H a then B else 0)) :
    (1/(S.card : ℝ))*∑ a∈S,f a≤
      A+((1/(S.card : ℝ))*∑ a∈S,(if H a then (1 : ℝ) else 0))*B := by
  have hc : (0 : ℝ)<S.card := by exact_mod_cast hp
  have hz : (S.card : ℝ)≠0 := ne_of_gt hc
  have hs : (∑ a∈S,f a)≤(S.card : ℝ)*A+(∑ a∈S,(if H a then (1 : ℝ) else 0))*B := by
    calc
      _ ≤ ∑ a∈S,(A+(if H a then B else 0)) := Finset.sum_le_sum h
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const,nsmul_eq_mul]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : H a <;> simp [ha]
  calc
    _ ≤ (1/(S.card : ℝ))*((S.card : ℝ)*A+(∑ a∈S,(if H a then (1 : ℝ) else 0))*B) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by field_simp [hz]

#print axioms actual_finite_average_indicator_bound
end Reference.MD06WalkExposure
