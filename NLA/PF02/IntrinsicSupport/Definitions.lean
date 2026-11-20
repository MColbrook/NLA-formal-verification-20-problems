module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Tactic
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Reference.PF02IntrinsicSupport
open Matrix Module
open scoped BigOperators MatrixOrder
abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)
def frame {k : ℕ} (U : Submodule ℝ (E k)) :
    Matrix (Fin k) (Fin (finrank ℝ U)) ℝ :=
  fun i j => (stdOrthonormalBasis ℝ U j : E k) i
end Reference.PF02IntrinsicSupport
