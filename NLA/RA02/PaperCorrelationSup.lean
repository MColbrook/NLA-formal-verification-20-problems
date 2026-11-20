module

public import NLA.RA02.PaperRationalSharpParameters
public import NLA.RA02.PaperCorrelationWitnesses

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem correlationCholeskyRatios_subset (r : ℕ) :
    correlationCholeskyRatios r ⊆ realPositiveCholeskyRatios r := by
  rintro x ⟨n,A,hA,hp,_,hr,ht,hx⟩
  exact ⟨n,A,hA,hp,hr,ht,hx⟩

theorem correlationLURatios_subset (r : ℕ) :
    correlationLURatios r ⊆ realPositiveLURatios r := by
  rintro x ⟨n,A,hA,hp,_,ht,hx⟩
  exact ⟨n,A,hA,hp,ht,hx⟩

theorem exists_correlation_cholesky_above (r : ℕ) (q : ℝ) (hq : q < (2 : ℝ)^r) :
    ∃ x ∈ correlationCholeskyRatios r, q < x := by
  obtain ⟨t,ht,hqA⟩ := rational_sharp_cholesky_parameter r q hq
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  let A := complexify (sharpFamily (r+1) (t : ℝ))
  have hA : A.PosDef := complexify_posDef _ (sharpFamily_posDef _ _ htR)
  have hp : ∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re := by
    intro i j
    exact ⟨rfl,sharpFamily_entry_pos r (t : ℝ) htR i j⟩
  obtain ⟨c,m,hc,hm,hd⟩ := rational_family_copy_counts r t ht
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have he : familyRankTail r (t : ℝ) = NLA.RA02.rankTail A hA.isHermitian r := by
    rw [familyRankTail,dif_pos hA.isHermitian]
  rw [he] at hqA
  have htA : 0 < NLA.RA02.rankTail A hA.isHermitian r := by
    rw [← he]
    exact familyRankTail_positive r htR
  exact exists_correlation_cholesky_above_of_copy_counts A hA.posSemidef hp
    m hm (c : ℝ) hcR hd r htA q hqA

theorem exists_correlation_lu_above (r : ℕ) (q : ℝ) (hq : q < (4 : ℝ)^r) :
    ∃ x ∈ correlationLURatios r, q < x := by
  obtain ⟨t,ht,hqA⟩ := rational_sharp_lu_parameter r q hq
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  let A := complexify (sharpFamily (r+1) (t : ℝ))
  have hA : A.PosDef := complexify_posDef _ (sharpFamily_posDef _ _ htR)
  have hp : ∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re := by
    intro i j
    exact ⟨rfl,sharpFamily_entry_pos r (t : ℝ) htR i j⟩
  obtain ⟨c,m,hc,hm,hd⟩ := rational_family_copy_counts r t ht
  have hcR : 0 < (c : ℝ) := by exact_mod_cast hc
  have htA : 0 < rectangularBestRankErrorSquared A r := by
    rw [rectangularBest_eq_squareBest,bestRankErrorSquared_eq_tail r A hA]
    change 0 < familySingularTailSquared r (t : ℝ)
    rw [familySingularTailSquared_eq r htR]
    exact sq_pos_of_pos (familyRankTail_positive r htR)
  exact exists_correlation_lu_above_of_copy_counts A hA.posSemidef hp
    m hm (c : ℝ) hcR hd r htA q hqA

theorem correlationCholeskyRatios_isLUB (r : ℕ) :
    IsLUB (correlationCholeskyRatios r) ((2 : ℝ)^r) := by
  constructor
  · intro x hx
    exact (realPositiveCholeskyRatios_isLUB r).1 (correlationCholeskyRatios_subset r hx)
  · intro y hy
    by_contra hle
    obtain ⟨x,hx,hxy⟩ := exists_correlation_cholesky_above r y (lt_of_not_ge hle)
    exact (not_lt_of_ge (hy hx)) hxy

theorem correlationLURatios_isLUB (r : ℕ) :
    IsLUB (correlationLURatios r) ((4 : ℝ)^r) := by
  constructor
  · intro x hx
    exact (realPositiveLURatios_isLUB r).1 (correlationLURatios_subset r hx)
  · intro y hy
    by_contra hle
    obtain ⟨x,hx,hxy⟩ := exists_correlation_lu_above r y (lt_of_not_ge hle)
    exact (not_lt_of_ge (hy hx)) hxy

theorem sharp_correlation_suprema (r : ℕ) :
    IsLUB (correlationCholeskyRatios r) ((2 : ℝ)^r) ∧
      IsLUB (correlationLURatios r) ((4 : ℝ)^r) :=
  ⟨correlationCholeskyRatios_isLUB r,correlationLURatios_isLUB r⟩

#print axioms sharp_correlation_suprema
end NLA.RA02.Paper
