module

public import NLA.TR04.RealSVD.Definitions
public import Mathlib.LinearAlgebra.Matrix.Kronecker

@[expose] public section

set_option autoImplicit false
namespace Reference.TensorGrouping
open Reference.RealSVDPackage
open scoped BigOperators Matrix Kronecker

variable {ι κ : Type*}

def grouped {m : ℕ} (A : Matrix (Fin m) (ι × κ) ℝ) :
    Matrix (Fin m × ι) κ ℝ := fun p j => A p.1 (p.2, j)

def entryFrobeniusSq {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℝ) : ℝ := ∑ i, ∑ j, A i j ^ 2

end Reference.TensorGrouping
