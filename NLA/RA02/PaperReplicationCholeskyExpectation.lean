module

public import NLA.RA02.PaperReplicationCholeskyWeights
public import NLA.RA02.PaperReplicationUpdates

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem finiteReplication_cholesky_expectation {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n)
    (hA : A.PosSemidef) (r : ℕ) :
    NLA.RA02.expectedTrace (finiteReplicatedMatrix m w A) r=NLA.RA02.expectedTrace A r := by
  induction r generalizing A with
  | zero => rw [NLA.RA02.expectedTrace_zero_steps,NLA.RA02.expectedTrace_zero_steps,finiteReplication_realTrace m w hw]
  | succ r ih =>
    by_cases ht : NLA.RA02.realTrace A=0
    · have hz := (NLA.RA02.realTrace_eq_zero_iff hA).mp ht
      subst A
      have hc : finiteReplicatedMatrix m w (0 : NLA.RA02.Square n)=0 := (finiteReplication_zero_iff m w hw _).mpr rfl
      rw [hc,(NLA.RA02.zero_residual (replicationDimension m) (r+1) []).2,(NLA.RA02.zero_residual n (r+1) []).2]
    · rw [NLA.RA02.expectedTrace_succ,NLA.RA02.expectedTrace_succ]
      have he : ∀ a : Fin (replicationDimension m),
          NLA.RA02.expectedTrace (NLA.RA02.choleskyStep (finiteReplicatedMatrix m w A) a) r=
            NLA.RA02.expectedTrace (NLA.RA02.choleskyStep A ((replicationLabels m).symm a).1) r := by
        intro a
        rw [finiteReplication_cholesky_update m w (copy_weights_ne_zero m w hw)]
        exact ih _ (NLA.RA02.choleskyStep_posSemidef A hA _)
      simp_rw [he]
      exact finiteReplication_cholesky_mass_sum m w hw A ht (fun i => NLA.RA02.expectedTrace (NLA.RA02.choleskyStep A i) r)

#print axioms finiteReplication_cholesky_expectation
end NLA.RA02.Paper
