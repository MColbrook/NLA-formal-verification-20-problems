module

public import NLA.RA09.Overlap
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open scoped BigOperators Classical
namespace NLA.RA09.Paper

/-- A constant tail permits the selected-weight bound using only column sums
and selected row sums. No matrix order or harmonic constraint is assumed. -/
theorem selected_average_bound {n : ℕ} (S : Finset (Fin n))
    (p : Fin n → Fin n → ℝ) (H : Fin n → ℝ) (r : ℝ)
    (hcol : ∀ j, ∑ i, p i j = 1)
    (hrow : ∀ i, ∑ j ∈ S, p i j ≤ 1)
    (hhead : ∀ i ∈ S, r ≤ H i) (htail : ∀ i ∉ S, H i = r) :
    (∑ j ∈ S, ∑ i, p i j * H i) ≤ ∑ i ∈ S, H i := by
  have hid (j : Fin n) : (∑ i, p i j * (H i-r)) = (∑ i, p i j*H i)-r := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hcol, one_mul]
  have hbound : (∑ i, ∑ j ∈ S, p i j*(H i-r)) ≤ ∑ i ∈ S, (H i-r) := by
    calc
      _ = ∑ i ∈ S, ∑ j ∈ S, p i j*(H i-r) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro i _ hi
        simp only [htail i hi, sub_self, mul_zero, Finset.sum_const_zero]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← Finset.sum_mul]
        exact (mul_le_mul_of_nonneg_right (hrow i) (sub_nonneg.mpr (hhead i hi))).trans_eq
          (one_mul _)
  calc
    _ = (∑ j ∈ S, ∑ i, p i j*(H i-r)) + ∑ j ∈ S, r := by
      simp only [hid, Finset.sum_sub_distrib]
      ring
    _ = (∑ i, ∑ j ∈ S, p i j*(H i-r)) + ∑ j ∈ S, r := by rw [Finset.sum_comm]
    _ ≤ (∑ i ∈ S, (H i-r)) + ∑ j ∈ S, r := add_le_add hbound le_rfl
    _ = _ := by rw [Finset.sum_sub_distrib]; ring

#print axioms selected_average_bound

end NLA.RA09.Paper
