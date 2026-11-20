module

public import NLA.RA02.PaperReplicationFiniteDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- Actual finite-index matrix c^{-1} P A P^* with the paper's inverse-square-root weights. -/
def replicatedCorrelation {n : ℕ} (m : Fin n → ℕ) (c : ℝ) (A : NLA.RA02.Square n) :
    NLA.RA02.Square (replicationDimension m) :=
  (c⁻¹ : ℝ) • finiteReplicatedMatrix m (fun i => (Real.sqrt (m i))⁻¹) A

end NLA.RA02.Paper
