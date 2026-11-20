module

public import NLA.RA09.Definitions

@[expose] public section

/-! Independent matrix specification for the Moore–Penrose harmonic lemma. -/
noncomputable section
namespace NLA.RA09

def spectralPseudoinverse {n : ℕ} (A : RealMatrix n) : RealMatrix n :=
  functionalCalculus (fun x : ℝ => x⁻¹) A

def IsMoorePenroseInverse {n : ℕ} (A P : RealMatrix n) : Prop :=
  A*P*A = A ∧ P*A*P = P ∧ (A*P).IsHermitian ∧ (P*A).IsHermitian

end NLA.RA09
