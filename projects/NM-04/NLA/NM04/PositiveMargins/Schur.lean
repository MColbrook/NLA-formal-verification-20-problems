module

public import NLA.NM04.PositiveMargins.Definitions
public import NLA.NM04.SchurMargins
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false

namespace NLA.NM04.PositiveMargins
noncomputable section
open scoped BigOperators Matrix

theorem schur_margins {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n) (a : Fin m → ℝ) (b : Fin n → ℝ) (τ : ℝ)
    (hx : S (firstIndex hm) (firstIndex hn) ≠ 0) (hS : Margins S a b)
    (ha : ∑ i, a i = τ) :
    (∀ i : Tail m, (∑ j : Tail n, schurTail S hm hn i j) =
      a i.val - a (firstIndex hm) * S i.val (firstIndex hn) /
        S (firstIndex hm) (firstIndex hn)) ∧
    (∀ j : Tail n, (∑ i : Tail m, schurTail S hm hn i j) =
      b j.val - b (firstIndex hn) * S (firstIndex hm) j.val /
        S (firstIndex hm) (firstIndex hn)) ∧
    (∑ i : Tail m, ∑ j : Tail n, schurTail S hm hn i j) =
      τ - a (firstIndex hm) * b (firstIndex hn) /
        S (firstIndex hm) (firstIndex hn) := by
  have hr (i : Tail m) : (∑ j : Tail n, schurTail S hm hn i j) =
      a i.val - a (firstIndex hm) * S i.val (firstIndex hn) /
        S (firstIndex hm) (firstIndex hn) := by
    simp_rw [schurTail, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    rw [sum_tail hn, sum_tail hn, hS.1, hS.1]
    field_simp [hx]
    ring
  refine ⟨hr, ?_, ?_⟩
  · intro j
    simp_rw [schurTail, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul]
    rw [sum_tail hm (fun i => S i j.val),
      sum_tail hm (fun i => S i (firstIndex hn)), hS.2, hS.2]
    field_simp [hx]
    ring
  · calc
      _ = ∑ i : Tail m, (a i.val - a (firstIndex hm) * S i.val (firstIndex hn) /
          S (firstIndex hm) (firstIndex hn)) := Finset.sum_congr rfl (fun i _ => hr i)
      _ = _ := by
        rw [sum_tail hm (fun i => a i - a (firstIndex hm) * S i (firstIndex hn) /
          S (firstIndex hm) (firstIndex hn))]
        simp only [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, hS.2, ha]
        field_simp [hx]
        ring

theorem schur_reconstruction {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (S : Rect m n) (a : Fin m → ℝ) (b : Fin n → ℝ) (τ : ℝ)
    (hx : S (firstIndex hm) (firstIndex hn) ≠ 0)
    (ha0 : a (firstIndex hm) ≠ 0) (hb0 : b (firstIndex hn) ≠ 0)
    (hS : Margins S a b) (ha : ∑ i, a i = τ) :
    tailMatrix S = schurTail S hm hn +
      (S (firstIndex hm) (firstIndex hn) / (a (firstIndex hm) * b (firstIndex hn))) •
        Matrix.vecMulVec
          (fun i : Tail m => a i.val - ∑ j : Tail n, schurTail S hm hn i j)
          (fun j : Tail n => b j.val - ∑ i : Tail m, schurTail S hm hn i j) := by
  obtain ⟨hr, hc, _⟩ := schur_margins hm hn S a b τ hx hS ha
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply]
  rw [hr i, hc j]
  simp only [tailMatrix, schurTail]
  field_simp [hx, ha0, hb0]
  ring

#print axioms schur_margins
#print axioms schur_reconstruction
end
end NLA.NM04.PositiveMargins
