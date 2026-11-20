module

public import NLA.RA02.PaperLUSupDefinitions
public import NLA.RA02.PaperRectangularBestAttainment
public import NLA.RA02.PaperMainLimits

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem rectangularBest_eq_squareBest {n : ℕ} (A : NLA.RA02.Square n) (r : ℕ) :
    rectangularBestRankErrorSquared A r = bestRankErrorSquared A r := rfl

theorem positive_rectangularBest_dimension {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ)
    (ht : 0 < rectangularBestRankErrorSquared A r) : r ≤ n := by
  rw [rectangularBest_eq_gramTail] at ht
  by_contra hr
  have hz : gramTail A r = 0 := by
    unfold gramTail NLA.RA02.rankTail
    apply Finset.sum_eq_zero
    intro i hi
    have hri := (Finset.mem_filter.mp hi).2
    have hin := i.isLt
    omega
  linarith

theorem lu_expectedError_best_upper_positive {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℂ) (r : ℕ)
    (ht : 0 < rectangularBestRankErrorSquared A r) :
    NLA.RA03.expectedError A r ≤ (4:ℝ)^r*rectangularBestRankErrorSquared A r :=
  lu_expectedError_best_upper A r (positive_rectangularBest_dimension A r ht)

theorem realPositiveLURatios_subset (r : ℕ) : realPositiveLURatios r ⊆ luRatios r := by
  rintro x ⟨n,A,_,_,ht,hx⟩
  exact ⟨n,n,A,ht,hx⟩

theorem luRatios_upper (r : ℕ) : (4:ℝ)^r ∈ upperBounds (luRatios r) := by
  rintro x ⟨m,n,A,ht,rfl⟩
  exact (div_le_iff₀ ht).mpr (lu_expectedError_best_upper_positive A r ht)

theorem sharp_family_mem_realPositiveLURatios (r : ℕ) {t : ℝ} (ht : 0 < t) :
    NLA.RA03.expectedError (complexify (sharpFamily (r+1) t)) r /
      bestRankErrorSquared (complexify (sharpFamily (r+1) t)) r ∈ realPositiveLURatios r := by
  let A := complexify (sharpFamily (r+1) t)
  have hA : A.PosDef := complexify_posDef _ (sharpFamily_posDef _ _ ht)
  refine ⟨r+1,A,hA,?_,?_,?_⟩
  · intro i j
    exact ⟨rfl,sharpFamily_entry_pos r t ht i j⟩
  · rw [rectangularBest_eq_squareBest,bestRankErrorSquared_eq_tail r A hA]
    change 0 < familySingularTailSquared r t
    rw [familySingularTailSquared_eq r ht]
    exact sq_pos_of_pos (familyRankTail_positive r ht)
  · rw [rectangularBest_eq_squareBest]

theorem realPositiveLURatios_isLUB (r : ℕ) : IsLUB (realPositiveLURatios r) ((4:ℝ)^r) := by
  constructor
  · intro x hx
    exact luRatios_upper r (realPositiveLURatios_subset r hx)
  · intro y hy
    apply le_of_tendsto (sharp_lu_bestApprox_limit r)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hy (sharp_family_mem_realPositiveLURatios r ht)

theorem luRatios_isLUB (r : ℕ) : IsLUB (luRatios r) ((4:ℝ)^r) := by
  refine ⟨luRatios_upper r,?_⟩
  intro y hy
  apply (realPositiveLURatios_isLUB r).2
  intro x hx
  exact hy (realPositiveLURatios_subset r hx)

#print axioms luRatios_isLUB
end NLA.RA02.Paper
