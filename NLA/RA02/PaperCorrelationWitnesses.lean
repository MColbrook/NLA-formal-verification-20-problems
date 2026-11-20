module

public import NLA.RA02.PaperCorrelationRatioDefinitions
public import NLA.RA02.PaperReplicationRatios
public import NLA.RA02.PaperRatioLowerLimit
public import NLA.RA02.PaperCholeskySup
public import NLA.RA02.PaperLUSup

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Topology Matrix
open Filter
namespace NLA.RA02.Paper

theorem replicationDimension_ge {n : ℕ} (m : Fin n → ℕ) (hm : ∀ i, 0 < m i) :
    n ≤ replicationDimension m := by
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Nat.succ_le_iff.mpr (hm i))
  simpa [replicationDimension] using hs

theorem exists_correlation_cholesky_above_of_copy_counts {n : ℕ}
    (A : NLA.RA02.Square n) (hA : A.PosSemidef)
    (hp : ∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i) (c : ℝ) (hc : 0 < c)
    (hd : ∀ i, A i i = (((c*(m i : ℝ)) : ℝ) : ℂ)) (r : ℕ)
    (ht : 0 < NLA.RA02.rankTail A hA.isHermitian r) (q : ℝ)
    (hq : q < NLA.RA02.expectedTrace A r/NLA.RA02.rankTail A hA.isHermitian r) :
    ∃ x ∈ correlationCholeskyRatios r, q < x := by
  let C := replicatedCorrelation m c A
  have hC : C.PosSemidef := replicatedCorrelation_posSemidef m c hc A hA
  have hr : r ≤ replicationDimension m :=
    (positive_rankTail_dimension A hA.isHermitian r ht).trans (replicationDimension_ge m hm)
  have htC : 0 < NLA.RA02.rankTail C hC.isHermitian r := by
    rw [replicatedCorrelation_rankTail m hm c hc A hA r]
    exact mul_pos (inv_pos.mpr hc) ht
  have hqC : q < NLA.RA02.expectedTrace C r/NLA.RA02.rankTail C hC.isHermitian r := by
    rw [replicatedCorrelation_cholesky_ratio m hm c hc A hA r]
    exact hq
  have he := regularizedCorrelation_cholesky_ratio_lower C hC r hr htC q hqC
  have hdC := (regularizedCorrelation_tail_limit C hC r hr).eventually (eventually_gt_nhds htC)
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧
      q < NLA.RA02.expectedTrace (regularizedCorrelation C δ) r /
        hermitianRankTail (regularizedCorrelation C δ) r ∧
      0 < hermitianRankTail (regularizedCorrelation C δ) r := by
    filter_upwards [self_mem_nhdsWithin,he,hdC] with δ hδ hqδ hdδ
    exact ⟨hδ,hqδ,hdδ⟩
  obtain ⟨δ,hδ,hqδ,hdδ⟩ := hall.exists
  have hB := regularized_replicatedCorrelation_properties m hm c hc A hA hp hd hδ
  have hBC : (regularizedCorrelation C δ).IsHermitian := hB.1.isHermitian
  refine ⟨NLA.RA02.expectedTrace (regularizedCorrelation C δ) r /
      hermitianRankTail (regularizedCorrelation C δ) r,?_,hqδ⟩
  refine ⟨replicationDimension m,regularizedCorrelation C δ,hB.1,hB.2.1,hB.2.2,hr,?_,?_⟩
  · simpa only [hermitianRankTail,dif_pos hBC] using hdδ
  · simp only [hermitianRankTail,dif_pos hBC]

theorem exists_correlation_lu_above_of_copy_counts {n : ℕ}
    (A : NLA.RA02.Square n) (hA : A.PosSemidef)
    (hp : ∀ i j, (A i j).im = 0 ∧ 0 < (A i j).re)
    (m : Fin n → ℕ) (hm : ∀ i, 0 < m i) (c : ℝ) (hc : 0 < c)
    (hd : ∀ i, A i i = (((c*(m i : ℝ)) : ℝ) : ℂ)) (r : ℕ)
    (ht : 0 < rectangularBestRankErrorSquared A r) (q : ℝ)
    (hq : q < NLA.RA03.expectedError A r/rectangularBestRankErrorSquared A r) :
    ∃ x ∈ correlationLURatios r, q < x := by
  let C := replicatedCorrelation m c A
  have hC : C.PosSemidef := replicatedCorrelation_posSemidef m c hc A hA
  have hr : r ≤ replicationDimension m :=
    (positive_rectangularBest_dimension A r ht).trans (replicationDimension_ge m hm)
  have htC : 0 < rectangularBestRankErrorSquared C r := by
    rw [replicatedCorrelation_best_error m hm c A r]
    exact mul_pos (sq_pos_of_pos (inv_pos.mpr hc)) ht
  have hqC : q < NLA.RA03.expectedError C r/rectangularBestRankErrorSquared C r := by
    rw [replicatedCorrelation_lu_ratio m hm c hc A r]
    exact hq
  have he := regularizedCorrelation_lu_ratio_lower C hC r hr htC q hqC
  have hdC := (regularizedCorrelation_best_error_limit C hC r hr).eventually (eventually_gt_nhds htC)
  have hall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧
      q < NLA.RA03.expectedError (regularizedCorrelation C δ) r /
        rectangularBestRankErrorSquared (regularizedCorrelation C δ) r ∧
      0 < rectangularBestRankErrorSquared (regularizedCorrelation C δ) r := by
    filter_upwards [self_mem_nhdsWithin,he,hdC] with δ hδ hqδ hdδ
    exact ⟨hδ,hqδ,hdδ⟩
  obtain ⟨δ,hδ,hqδ,hdδ⟩ := hall.exists
  have hB := regularized_replicatedCorrelation_properties m hm c hc A hA hp hd hδ
  refine ⟨NLA.RA03.expectedError (regularizedCorrelation C δ) r /
      rectangularBestRankErrorSquared (regularizedCorrelation C δ) r,?_,hqδ⟩
  exact ⟨replicationDimension m,regularizedCorrelation C δ,hB.1,hB.2.1,hB.2.2,hdδ,rfl⟩

#print axioms exists_correlation_lu_above_of_copy_counts
end NLA.RA02.Paper
