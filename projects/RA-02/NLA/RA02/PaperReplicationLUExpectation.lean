module

public import NLA.RA02.PaperReplicationLUWeights
public import NLA.RA02.PaperReplicationUpdates
public import NLA.RA02.PaperLUNonnegative

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem finiteReplication_lu_expectation {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n) (r : ℕ) :
    NLA.RA03.expectedError (finiteReplicatedMatrix m w A) r=NLA.RA03.expectedError A r := by
  induction r generalizing A with
  | zero => rw [lu_expectedError_zero,lu_expectedError_zero,finiteReplication_frobenius m w hw]
  | succ r ih =>
    rw [lu_expectedError_succ,lu_expectedError_succ,Fintype.sum_option,Fintype.sum_option]
    simp only [NLA.RA03.nextResidual,lu_expectedError_zero_matrix,mul_zero,zero_add]
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
    simp_rw [finiteReplication_lu_update m w (copy_weights_ne_zero m w hw),ih]
    exact finiteReplication_lu_mass_sum m w hw A (fun i j => NLA.RA03.expectedError (NLA.RA03.pivotResidual A (i,j)) r)

#print axioms finiteReplication_lu_expectation
end NLA.RA02.Paper
