module

public import NLA.NM04.PositiveMargins.Definitions
public import NLA.NM04.MinorLinearity
public import Mathlib.Tactic
public import Mathlib.Tactic.Ring

@[expose] public section

set_option autoImplicit false

namespace NLA.NM04.PositiveMargins
noncomputable section
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
universe u v
variable {α : Type u} {β : Type v}
variable [Fintype α] [Fintype β] [LinearOrder α] [LinearOrder β]

theorem lower_smul (a : α → ℝ) (b : β → ℝ) (f : MinorIndex α β → ℝ)
    (x : ℝ) (I : MinorIndex α β) :
    lower a b (fun J => x * f J) I = x * lower a b f I := by
  simp only [lower, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem column_smul (b : β → ℝ) (f : MinorIndex α β → ℝ)
    (x : ℝ) (I : MinorIndex α β) :
    column b (fun J => x * f J) I = x * column b f I := by
  simp only [column, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem row_smul (a : α → ℝ) (f : MinorIndex α β → ℝ)
    (x : ℝ) (I : MinorIndex α β) :
    row a (fun J => x * f J) I = x * row a f I := by
  simp only [row, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem action_smul (a : α → ℝ) (b : β → ℝ) (τ : ℝ)
    (f : MinorIndex α β → ℝ) (x : ℝ) (I : MinorIndex α β) :
    action a b τ (fun J => x * f J) I = x * action a b τ f I := by
  simp only [action, raising_smul, lower_smul, column_smul, row_smul]
  ring

private theorem routed_pair_sum {D E K : Type*}
    [Fintype D] [Fintype E] [Fintype K] [DecidableEq K]
    (address : D → E → K) (coefficient : D → E → ℝ) (f : K → ℝ) :
    (∑ J : K, (∑ s : D, ∑ t : E,
      if address s t = J then coefficient s t else 0) * f J) =
      ∑ s : D, ∑ t : E, coefficient s t * f (address s t) := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp

theorem G_mulVec (a : α → ℝ) (b : β → ℝ) (τ : ℝ)
    (f : MinorIndex α β → ℝ) (I : MinorIndex α β) :
    (G a b τ).mulVec f I = action a b τ f I := by
  simp only [G, Matrix.mulVec, dotProduct, add_mul, sub_mul,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [routed_pair_sum, routed_pair_sum, routed_pair_sum]
  simp only [action, lower, column, row, raising]
  congr 4
  simp

#print axioms lower_smul
#print axioms column_smul
#print axioms row_smul
#print axioms action_smul
#print axioms G_mulVec
end
end NLA.NM04.PositiveMargins
