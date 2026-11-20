module

public import NLA.RA02.PaperLUVectorIdentity

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

def vectorPivot {m : ℕ} (u y : Fin m → ℂ) (i : Fin m) : Fin m → ℂ :=
  if u i = 0 then y else fun j => y j-u j*y i/u i

theorem vectorPivot_entry_bound {m : ℕ} (u y : Fin m → ℂ) (i j : Fin m) :
    Complex.normSq (u i)*Complex.normSq (vectorPivot u y i j) ≤
      Complex.normSq (u i*y j-u j*y i) := by
  by_cases hi : u i = 0
  · simp only [hi, map_zero, zero_mul]
    exact Complex.normSq_nonneg _
  · apply le_of_eq
    rw [← Complex.normSq_mul]
    congr 1
    simp only [vectorPivot, if_neg hi]
    field_simp

theorem vectorPivot_weighted_bound {m : ℕ} (u y : Fin m → ℂ) :
    (∑ i, Complex.normSq (u i)*(∑ j, Complex.normSq (vectorPivot u y i j))) ≤
      2*(∑ i, Complex.normSq (u i))*(∑ j, Complex.normSq (y j)) -
        2*Complex.normSq (∑ i, star (u i)*y i) := by
  rw [← vector_cross_norm_identity u y]
  apply Finset.sum_le_sum
  intro i _
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => vectorPivot_entry_bound u y i j)

#print axioms vectorPivot_weighted_bound
end NLA.RA02.Paper
