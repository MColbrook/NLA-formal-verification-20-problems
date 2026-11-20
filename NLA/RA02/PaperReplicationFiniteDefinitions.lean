module

public import NLA.RA02.PaperReplicationDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace NLA.RA02.Paper

def replicationDimension {n : ℕ} (m : Fin n → ℕ) : ℕ := ∑ i, m i

/-- Identify the actual copy labels with the finite index type used by the algorithms. -/
def replicationLabels {n : ℕ} (m : Fin n → ℕ) :
    ReplicatedRows m ≃ Fin (replicationDimension m) :=
  (Fintype.equivFin (ReplicatedRows m)).trans (finCongr (by
    simp [ReplicatedRows,Fintype.card_sigma,replicationDimension]))

def finiteRowReplication {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ) :
    Matrix (Fin (replicationDimension m)) (Fin n) ℂ :=
  (rowReplication m w).submatrix (replicationLabels m).symm id

def finiteReplicatedMatrix {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (A : NLA.RA02.Square n) : NLA.RA02.Square (replicationDimension m) :=
  finiteRowReplication m w * A * (finiteRowReplication m w).conjTranspose

end NLA.RA02.Paper
