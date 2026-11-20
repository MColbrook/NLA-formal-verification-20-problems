module

public import NLA.RA09.PaperDefinitions
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace RootRA09ThresholdTrace
open NLA.RA09

def thresholdAuxiliary (f : ℝ → ℝ) (τ a : ℝ) : ℝ :=
  max (2*(transferScale f τ)^2*a^2-(f a)^2) ((f τ)^2)

def selectedProjector {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) (k : ℕ) : RealMatrix n :=
  spectralCombination d (fun i => if i.val < k then 1 else 0)

def eigenvector {n : ℕ} {A : RealMatrix n} (d : OrderedSpectralData A) (j : Fin n) : Fin n → ℝ :=
  fun i => (d.orthogonal : RealMatrix n) i j

end RootRA09ThresholdTrace
