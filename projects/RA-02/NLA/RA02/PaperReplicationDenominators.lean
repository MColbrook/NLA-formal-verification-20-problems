module

public import NLA.RA02.PaperReplicatedCorrelation
public import NLA.RA02.PaperTailIsometricEmbedding
public import NLA.RA02.PaperTailScaling

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem replicatedCorrelation_best_error {n : ℕ} (m : Fin n → ℕ)
    (hm : ∀ i, 0 < m i) (c : ℝ) (A : NLA.RA02.Square n) (r : ℕ) :
    rectangularBestRankErrorSquared (replicatedCorrelation m c A) r =
      (c⁻¹)^2*rectangularBestRankErrorSquared A r := by
  unfold replicatedCorrelation
  rw [rectangularBest_real_smul]
  unfold finiteReplicatedMatrix
  rw [rectangularBest_isometric_embedding (finiteRowReplication m _) (finiteRowReplication_isometry m _ (sqrtReplication_weights m hm))]

theorem replicatedCorrelation_rankTail {n : ℕ} (m : Fin n → ℕ)
    (hm : ∀ i, 0 < m i) (c : ℝ) (hc : 0 < c)
    (A : NLA.RA02.Square n) (hA : A.PosSemidef) (r : ℕ) :
    NLA.RA02.rankTail (replicatedCorrelation m c A)
      (replicatedCorrelation_posSemidef m c hc A hA).isHermitian r =
      c⁻¹*NLA.RA02.rankTail A hA.isHermitian r := by
  have hP := finiteRowReplication_isometry m (fun i => (Real.sqrt (m i))⁻¹) (sqrtReplication_weights m hm)
  have hC := finiteReplicatedMatrix_posSemidef m (fun i => (Real.sqrt (m i))⁻¹) A hA
  unfold replicatedCorrelation
  rw [rankTail_real_smul c⁻¹ (inv_nonneg.mpr hc.le) _ hC]
  unfold finiteReplicatedMatrix
  rw [rankTail_isometric_embedding (finiteRowReplication m _) hP A hA]

#print axioms replicatedCorrelation_rankTail
end NLA.RA02.Paper
