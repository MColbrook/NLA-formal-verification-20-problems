module

public import NLA.TR27.PaperProjectionDefinitions
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
namespace NLA.TR27.Paper

def centerHankel (r : ℕ) (a : Fin r → ℂ) : Matrix (Fin (r+2)) (Fin (r+2)) ℂ :=
  fun i j => (if i.val+j.val = 1 then 1 else 0) - ∑ l, a l ^ (i.val+j.val)

/-- Swap the first two coordinates and negate every remaining coordinate. -/
def signatureMatrix (r : ℕ) : Matrix (Fin (r+2)) (Fin (r+2)) ℂ := fun i =>
  Fin.cons (if i = 1 then 1 else 0)
    (Fin.cons (if i = 0 then 1 else 0)
      (fun j : Fin r => if i = j.succ.succ then -1 else 0))

/-- Actual Hankel coordinates in the source vector space. -/
def sourceHankel {D : ℕ} (n : ℕ) (hD : 2*n ≤ D) (v : CurveSpace D) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℂ :=
  fun i j => v ⟨i.val+j.val, by omega⟩

end NLA.TR27.Paper
