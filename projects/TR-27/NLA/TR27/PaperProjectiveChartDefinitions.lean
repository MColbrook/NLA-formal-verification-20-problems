module

public import NLA.TR27.PaperProjectiveTopologyDefinitions
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped LinearAlgebra.Projectivization
namespace NLA.TR27.Paper

def projectiveCoordinateRatio {n : ℕ} (i j : Fin n) (p : ℙ ℂ (Fin n → ℂ)) : ℂ :=
  p.rep j / p.rep i

def projectiveChartInverse {n : ℕ} (i : Fin (n+1)) (v : Fin n → ℂ) : ℙ ℂ (Fin (n+1) → ℂ) :=
  Projectivization.mk ℂ (Fin.insertNth i 1 v) (by
    intro hz
    have h := congrFun hz i
    simpa using h)

end NLA.TR27.Paper
