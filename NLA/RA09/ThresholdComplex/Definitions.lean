module

public import NLA.RA09.ThresholdTrace.Definitions
public import NLA.RA09.ComplexDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace RootRA09ThresholdComplex
open NLA.RA09.ComplexPaper

def selectedProjector {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) (k : ℕ) : ComplexMatrix n :=
  spectralCombination d (fun i => if i.val < k then 1 else 0)

def eigenvector {n : ℕ} {A : ComplexMatrix n} (d : OrderedSpectralData A) (j : Fin n) : Fin n → ℂ :=
  fun i => (d.unitary : ComplexMatrix n) i j

def outerSquare {n : ℕ} (v : Fin n → ℂ) : ComplexMatrix n := Matrix.vecMulVec v (star v)

end RootRA09ThresholdComplex
