module

public import NLA.RA02.PaperReplicationDenominators
public import NLA.RA02.PaperReplicationLUExpectation
public import NLA.RA02.PaperReplicationCholeskyExpectation
public import NLA.RA02.PaperCholeskyScaling

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem replicatedCorrelation_lu_expectation {n : ℕ} (m : Fin n → ℕ)
    (hm : ∀ i, 0 < m i) (c : ℝ) (A : NLA.RA02.Square n) (r : ℕ) :
    NLA.RA03.expectedError (replicatedCorrelation m c A) r=(c⁻¹)^2*NLA.RA03.expectedError A r := by
  unfold replicatedCorrelation
  rw [lu_expectedError_real_smul,finiteReplication_lu_expectation m _ (sqrtReplication_weights m hm)]

theorem replicatedCorrelation_cholesky_expectation {n : ℕ} (m : Fin n → ℕ)
    (hm : ∀ i, 0 < m i) (c : ℝ) (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (r : ℕ) :
    NLA.RA02.expectedTrace (replicatedCorrelation m c A) r=c⁻¹*NLA.RA02.expectedTrace A r := by
  unfold replicatedCorrelation
  rw [cholesky_expectedTrace_real_smul,finiteReplication_cholesky_expectation m _ (sqrtReplication_weights m hm) A hA]

theorem replicatedCorrelation_lu_ratio {n : ℕ} (m : Fin n → ℕ)
    (hm : ∀ i, 0 < m i) (c : ℝ) (hc : 0 < c) (A : NLA.RA02.Square n) (r : ℕ) :
    NLA.RA03.expectedError (replicatedCorrelation m c A) r /
      rectangularBestRankErrorSquared (replicatedCorrelation m c A) r =
        NLA.RA03.expectedError A r / rectangularBestRankErrorSquared A r := by
  rw [replicatedCorrelation_lu_expectation m hm c A r,replicatedCorrelation_best_error m hm c A r]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (inv_ne_zero (ne_of_gt hc)))

theorem replicatedCorrelation_cholesky_ratio {n : ℕ} (m : Fin n → ℕ)
    (hm : ∀ i, 0 < m i) (c : ℝ) (hc : 0 < c)
    (A : NLA.RA02.Square n) (hA : A.PosSemidef) (r : ℕ) :
    NLA.RA02.expectedTrace (replicatedCorrelation m c A) r /
      NLA.RA02.rankTail (replicatedCorrelation m c A)
        (replicatedCorrelation_posSemidef m c hc A hA).isHermitian r =
      NLA.RA02.expectedTrace A r / NLA.RA02.rankTail A hA.isHermitian r := by
  rw [replicatedCorrelation_cholesky_expectation m hm c A hA r,
    replicatedCorrelation_rankTail m hm c hc A hA r]
  exact mul_div_mul_left _ _ (inv_ne_zero (ne_of_gt hc))

#print axioms replicatedCorrelation_lu_ratio
#print axioms replicatedCorrelation_cholesky_ratio
end NLA.RA02.Paper
