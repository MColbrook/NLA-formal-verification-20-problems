module

public import NLA.RA02.PaperCholeskySupDefinitions
public import NLA.RA02.PaperCholeskyUpper
public import NLA.RA02.PaperRankTailLimit

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology
open Filter
namespace NLA.RA02.Paper

theorem positive_rankTail_dimension {n : ℕ} (A : NLA.RA02.Square n)
    (hA : A.IsHermitian) (r : ℕ) (ht : 0 < NLA.RA02.rankTail A hA r) : r ≤ n := by
  by_contra hr
  have hz : NLA.RA02.rankTail A hA r = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hri := (Finset.mem_filter.mp hi).2
    have hin := i.isLt
    omega
  linarith

theorem choleskyRatios_membership (r : ℕ) (x : ℝ) :
    x ∈ choleskyRatios r ↔ ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosSemidef),
      0 < NLA.RA02.rankTail A hA.isHermitian r ∧
      x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r := by
  constructor
  · rintro ⟨n,A,hA,_,ht,hx⟩
    exact ⟨n,A,hA,ht,hx⟩
  · rintro ⟨n,A,hA,ht,hx⟩
    exact ⟨n,A,hA,positive_rankTail_dimension A hA.isHermitian r ht,ht,hx⟩

theorem realPositiveCholeskyRatios_membership (r : ℕ) (x : ℝ) :
    x ∈ realPositiveCholeskyRatios r ↔ ∃ (n : ℕ) (A : NLA.RA02.Square n) (hA : A.PosDef),
      (∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re) ∧
      0 < NLA.RA02.rankTail A hA.isHermitian r ∧
      x = NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r := by
  constructor
  · rintro ⟨n,A,hA,hpos,_,ht,hx⟩
    exact ⟨n,A,hA,hpos,ht,hx⟩
  · rintro ⟨n,A,hA,hpos,ht,hx⟩
    exact ⟨n,A,hA,hpos,positive_rankTail_dimension A hA.isHermitian r ht,ht,hx⟩

theorem realPositiveCholeskyRatios_subset (r : ℕ) :
    realPositiveCholeskyRatios r ⊆ choleskyRatios r := by
  rintro x ⟨n,A,hA,_,hr,ht,hx⟩
  exact ⟨n,A,hA.posSemidef,hr,ht,hx⟩

theorem choleskyRatios_upper (r : ℕ) : (2:ℝ)^r ∈ upperBounds (choleskyRatios r) := by
  rintro x ⟨n,A,hA,hr,ht,rfl⟩
  exact (div_le_iff₀ ht).mpr (cholesky_expectedTrace_upper A hA r hr)

theorem sharp_family_mem_realPositiveCholeskyRatios (r : ℕ) {t : ℝ} (ht : 0 < t) :
    NLA.RA02.expectedTrace (complexify (sharpFamily (r+1) t)) r / familyRankTail r t ∈
      realPositiveCholeskyRatios r := by
  let A := complexify (sharpFamily (r+1) t)
  have hA : A.PosDef := complexify_posDef _ (sharpFamily_posDef _ _ ht)
  have he : familyRankTail r t = NLA.RA02.rankTail A hA.isHermitian r := by
    rw [familyRankTail, dif_pos hA.isHermitian]
  refine ⟨r+1,A,hA,?_,by omega,?_,?_⟩
  · intro i j
    exact ⟨rfl, sharpFamily_entry_pos r t ht i j⟩
  · rw [← he]
    exact familyRankTail_positive r ht
  · rw [he]

theorem realPositiveCholeskyRatios_isLUB (r : ℕ) :
    IsLUB (realPositiveCholeskyRatios r) ((2:ℝ)^r) := by
  constructor
  · intro x hx
    exact choleskyRatios_upper r (realPositiveCholeskyRatios_subset r hx)
  · intro y hy
    apply le_of_tendsto (sharp_cholesky_rankTail_limit r)
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact hy (sharp_family_mem_realPositiveCholeskyRatios r ht)

theorem choleskyRatios_isLUB (r : ℕ) : IsLUB (choleskyRatios r) ((2:ℝ)^r) := by
  refine ⟨choleskyRatios_upper r, ?_⟩
  intro y hy
  apply (realPositiveCholeskyRatios_isLUB r).2
  intro x hx
  exact hy (realPositiveCholeskyRatios_subset r hx)

#print axioms choleskyRatios_isLUB
end NLA.RA02.Paper
