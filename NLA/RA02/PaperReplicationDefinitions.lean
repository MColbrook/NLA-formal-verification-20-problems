module

public import NLA.RA02.PaperCorrelationDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA02.Paper

/-- Labels for the actual copies of each original row. -/
abbrev ReplicatedRows {n : ℕ} (m : Fin n → ℕ) := Σ i : Fin n, Fin (m i)

/-- Every copy of row i receives the same real weight. The correlation
construction uses w i = 1 / sqrt(m i). -/
def rowReplication {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ) :
    Matrix (ReplicatedRows m) (Fin n) ℂ :=
  fun a j => if a.1 = j then (w j : ℂ) else 0

/-- The literal replicated matrix before the common scalar normalization. -/
def replicatedMatrix {n : ℕ} (m : Fin n → ℕ) (w : Fin n → ℝ)
    (A : NLA.RA02.Square n) : Matrix (ReplicatedRows m) (ReplicatedRows m) ℂ :=
  rowReplication m w * A * (rowReplication m w).conjTranspose

end NLA.RA02.Paper
