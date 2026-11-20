module

public import NLA.RA02.PaperReplicationLUWeights
public import NLA.RA02.FiniteExpectation

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem finiteReplication_realTrace {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n) :
    NLA.RA02.realTrace (finiteReplicatedMatrix m w A)=NLA.RA02.realTrace A :=
  congrArg Complex.re (finiteReplicatedMatrix_trace m w hw A)

theorem finiteReplication_diagonal_real {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (A : NLA.RA02.Square n) (a : Fin (replicationDimension m)) :
    (finiteReplicatedMatrix m w A a a).re =
      (w ((replicationLabels m).symm a).1)^2*(A ((replicationLabels m).symm a).1 ((replicationLabels m).symm a).1).re := by
  rw [finiteReplicatedMatrix_entry]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,zero_mul,sub_zero,add_zero,pow_two]
  ring

theorem finiteReplication_cholesky_mass_sum {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n)
    (ht : NLA.RA02.realTrace A ≠ 0) (F : Fin n → ℝ) :
    (∑ a : Fin (replicationDimension m), NLA.RA02.pivotMass (finiteReplicatedMatrix m w A) a*
      F ((replicationLabels m).symm a).1) = ∑ i, NLA.RA02.pivotMass A i*F i := by
  have htc : NLA.RA02.realTrace (finiteReplicatedMatrix m w A) ≠ 0 := by
    rw [finiteReplication_realTrace m w hw]
    exact ht
  simp only [NLA.RA02.pivotMass,if_neg htc,if_neg ht,
    finiteReplication_realTrace m w hw,finiteReplication_diagonal_real]
  have he : ∀ a : Fin (replicationDimension m),
      (w ((replicationLabels m).symm a).1)^2*(A ((replicationLabels m).symm a).1 ((replicationLabels m).symm a).1).re /
        NLA.RA02.realTrace A*F ((replicationLabels m).symm a).1 =
      (w ((replicationLabels m).symm a).1)^2*
        ((A ((replicationLabels m).symm a).1 ((replicationLabels m).symm a).1).re /
          NLA.RA02.realTrace A*F ((replicationLabels m).symm a).1) := by
    intro a
    ring
  simp_rw [he]
  exact sum_copy_weights m w hw (fun i => (A i i).re/NLA.RA02.realTrace A*F i)

#print axioms finiteReplication_cholesky_mass_sum
end NLA.RA02.Paper
