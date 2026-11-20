module

public import NLA.RA02.PaperSharpDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace NLA.RA02.Paper

def nextColumn {n s : ℕ} (hs : s < n) (t : ℝ) : Fin n → ℝ :=
  fun i => lower n t i ⟨s,hs⟩

def interpolationCoefficients {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Fin s → ℝ := (prefixMatrix hs.le rows t)⁻¹ *ᵥ (fun i => nextColumn hs t (rows i))

def interpolationResidual {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) :
    Fin n → ℝ := nextColumn hs t -
      ((lower n t).submatrix id (Fin.castLE hs.le)) *ᵥ interpolationCoefficients hs rows t

def interpolationSquaredNorm {n s : ℕ} (hs : s < n) (rows : Fin s ↪ Fin n) (t : ℝ) : ℝ :=
  ∑ i : Fin n, (interpolationResidual hs rows t i)^2

end NLA.RA02.Paper
