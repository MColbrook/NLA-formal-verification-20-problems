module

public import NLA.RA02.PaperHeadProbe

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem eigenvalue_le_total {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (i : Fin n) :
    a i ≤ ∑ j, a j := by
  exact Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)

theorem weighted_head_le_total {n : ℕ} (k : ℕ) (a : Fin n → ℝ) (v : Fin n → ℂ)
    (ha : ∀ i, 0 ≤ a i) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i*Complex.normSq (v i)) ≤
      (∑ i, a i)*headEnergy k v := by
  unfold headEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_right (eigenvalue_le_total a ha i) (Complex.normSq_nonneg _)

theorem headEnergy_nonneg {n : ℕ} (k : ℕ) (v : Fin n → ℂ) : 0 ≤ headEnergy k v := by
  exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)

theorem weighted_head_eq_zero {n : ℕ} (k : ℕ) (a : Fin n → ℝ) (v : Fin n → ℂ)
    (ha : ∀ i, 0 ≤ a i) (hh : headEnergy k v = 0) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i*Complex.normSq (v i)) = 0 := by
  apply le_antisymm
  · simpa [hh] using weighted_head_le_total k a v ha
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (Complex.normSq_nonneg _))

theorem weighted_head_tail_split {n : ℕ} (k : ℕ) (a : Fin n → ℝ) (v : Fin n → ℂ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), a i*Complex.normSq (v i)) +
      (∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), a i*Complex.normSq (v i)) =
      ∑ i, a i*Complex.normSq (v i) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < k <;> simp [hi, Nat.not_lt.mp, Nat.not_le.mpr, *]

#print axioms weighted_head_le_total
end NLA.RA02.Paper
