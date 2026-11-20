module

public import NLA.RA02.PaperReplicationFiniteDefinitions
public import NLA.RA02.PaperReplicationMatrix

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open scoped BigOperators Classical ComplexOrder Matrix
namespace NLA.RA02.Paper

theorem finiteRowReplication_isometry {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) :
    (finiteRowReplication m w).conjTranspose*finiteRowReplication m w=1 := by
  ext i j
  change (∑ a : Fin (replicationDimension m),
    star (rowReplication m w ((replicationLabels m).symm a) i)*
      rowReplication m w ((replicationLabels m).symm a) j) = (1 : NLA.RA02.Square n) i j
  rw [(replicationLabels m).symm.sum_comp
    (fun a => star (rowReplication m w a i)*rowReplication m w a j)]
  exact congrArg (fun M : NLA.RA02.Square n => M i j) (rowReplication_isometry m w hw)

theorem finiteReplicatedMatrix_entry {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (A : NLA.RA02.Square n) (a b : Fin (replicationDimension m)) :
    finiteReplicatedMatrix m w A a b =
      (w ((replicationLabels m).symm a).1 : ℂ)*
        A ((replicationLabels m).symm a).1 ((replicationLabels m).symm b).1*
          (w ((replicationLabels m).symm b).1 : ℂ) :=
  replicatedMatrix_entry m w A ((replicationLabels m).symm a) ((replicationLabels m).symm b)

theorem finiteReplicatedMatrix_posSemidef {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (A : NLA.RA02.Square n) (hA : A.PosSemidef) :
    (finiteReplicatedMatrix m w A).PosSemidef :=
  hA.mul_mul_conjTranspose_same (finiteRowReplication m w)

theorem finiteReplicatedMatrix_trace {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, (m i : ℝ)*(w i)^2=1) (A : NLA.RA02.Square n) :
    (finiteReplicatedMatrix m w A).trace=A.trace := by
  rw [finiteReplicatedMatrix,Matrix.trace_mul_cycle,finiteRowReplication_isometry m w hw,Matrix.one_mul]

#print axioms finiteRowReplication_isometry
end NLA.RA02.Paper
