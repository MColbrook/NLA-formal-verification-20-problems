module

public import NLA.MD06.GraphCriticalityHessian.Definitions

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Reference.MD06Actual
open scoped BigOperators

theorem sum_ordered_pairs {n : ℕ} (f : Fin n → Fin n → ℝ) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
  classical
  have hsplit : ∀ i j, f i j = (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with hi | hi | hi
    · simp only [if_pos hi,if_neg (not_lt_of_gt hi),add_zero]
    · subst j
      simp only [lt_self_iff_false,if_false,hdiag,add_zero]
    · simp only [if_pos hi,if_neg (not_lt_of_gt hi),zero_add]
  have hlower : (∑ i, ∑ j, if j < i then f i j else 0) =
      ∑ i, ∑ j, if i < j then f j i else 0 := by
    rw [Finset.sum_comm]
  calc
    (∑ i, ∑ j, f i j) = ∑ i, ∑ j,
        ((if i < j then f i j else 0) + (if j < i then f i j else 0)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_congr rfl (fun j _ => hsplit i j)
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f i j else 0) := by simp only [Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if i < j then f j i else 0) := by rw [hlower]
    _ = ∑ i, ∑ j, if i < j then f i j + f j i else 0 := by
      simp only [← Finset.sum_add_distrib,ite_add_ite,add_zero]

#print axioms sum_ordered_pairs
end Reference.MD06Actual
