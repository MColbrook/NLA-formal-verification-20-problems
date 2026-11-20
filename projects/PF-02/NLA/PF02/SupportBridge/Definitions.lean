module

/- Actual finite real PSD support definitions. Separate reference extension. -/
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.PF02Support
open Matrix
open scoped BigOperators MatrixOrder

abbrev Mat (n : Type*) := Matrix n n ℝ
abbrev Vector (n : Type*) := EuclideanSpace ℝ n

def lin {n : Type*} [Fintype n] [DecidableEq n] (A : Mat n) :
    Vector n →ₗ[ℝ] Vector n := Matrix.toEuclideanLin A

def kernel {n : Type*} [Fintype n] [DecidableEq n] (A : Mat n) :
    Submodule ℝ (Vector n) := LinearMap.ker (lin A)

def image {n : Type*} [Fintype n] [DecidableEq n] (A : Mat n) :
    Submodule ℝ (Vector n) := LinearMap.range (lin A)

def SupportedOn {n : Type*} [Fintype n] [DecidableEq n]
    (A : Mat n) (U : Submodule ℝ (Vector n)) : Prop := image A ≤ U

end Reference.PF02Support
