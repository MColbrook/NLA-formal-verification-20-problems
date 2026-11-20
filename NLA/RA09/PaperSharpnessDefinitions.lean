module

public import NLA.RA09.PaperDefinitions

@[expose] public section

/-! Independent sharpness specification in actual matrix quantities. -/
noncomputable section
namespace NLA.RA09

def UnorderedSharpnessWitness (γ : ℝ) : Prop :=
  ∃ (n : ℕ) (hn : 1 < n) (p : ℝ) (A B : RealMatrix n)
      (dA : OrderedSpectralData A) (dB : OrderedSpectralData B),
    0 < p ∧ p < 1 ∧ B.rank ≤ 1 ∧ dA.eigenvalues ⟨1,hn⟩ = 1 ∧
    0 < spectralTail dA 1 ∧
    0 < frobeniusSquared (A-B) - spectralTail dA 1 ∧
    0 < frobeniusNorm (A-B) / Real.sqrt (spectralTail dA 1) - 1 ∧
    γ * (frobeniusSquared (A-B) - spectralTail dA 1) <
      frobeniusSquared (functionalCalculus (fun x : ℝ => x^p) A -
        functionTruncation dB (fun x : ℝ => x^p) 1) -
      functionTail dA (fun x : ℝ => x^p) 1 ∧
    γ * (frobeniusNorm (A-B) / Real.sqrt (spectralTail dA 1) - 1) <
      frobeniusNorm (functionalCalculus (fun x : ℝ => x^p) A -
        functionTruncation dB (fun x : ℝ => x^p) 1) /
          Real.sqrt (functionTail dA (fun x : ℝ => x^p) 1) - 1

end NLA.RA09
