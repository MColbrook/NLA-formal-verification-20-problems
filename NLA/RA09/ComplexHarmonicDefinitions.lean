module

public import NLA.RA09.ComplexDefinitions

@[expose] public section

/-! Independent matrix specification for the Moore–Penrose harmonic lemma. -/
noncomputable section
namespace NLA.RA09.ComplexPaper

def spectralPseudoinverse {n : ℕ} (A : ComplexMatrix n) : ComplexMatrix n :=
  functionalCalculus (fun x : ℝ => x⁻¹) A

def IsMoorePenroseInverse {n : ℕ} (A P : ComplexMatrix n) : Prop :=
  A*P*A = A ∧ P*A*P = P ∧ (A*P).IsHermitian ∧ (P*A).IsHermitian

end NLA.RA09.ComplexPaper
