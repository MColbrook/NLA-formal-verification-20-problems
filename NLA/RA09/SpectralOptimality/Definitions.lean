module

public import NLA.RA09.ComplexDefinitions
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace RootRA09SpectralOptimality
def selectedProjector {n : ℕ} {A : NLA.RA09.RealMatrix n}
    (d : NLA.RA09.OrderedSpectralData A) (k : ℕ) : NLA.RA09.RealMatrix n :=
  NLA.RA09.spectralCombination d (fun i => if i.val < k then 1 else 0)
def complexSelectedProjector {n : ℕ} {A : NLA.RA09.ComplexPaper.ComplexMatrix n}
    (d : NLA.RA09.ComplexPaper.OrderedSpectralData A) (k : ℕ) : NLA.RA09.ComplexPaper.ComplexMatrix n :=
  NLA.RA09.ComplexPaper.spectralCombination d (fun i => if i.val < k then 1 else 0)
end RootRA09SpectralOptimality
