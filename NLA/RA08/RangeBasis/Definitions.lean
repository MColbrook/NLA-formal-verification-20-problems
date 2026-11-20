module

public import NLA.RA08.PaperDefinitions
public import Mathlib.LinearAlgebra.Matrix.ToLin

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper.RangeBasis

def FullColumns {n l : ℕ} (Ω : Matrix (Fin n) (Fin l) ℝ) : Prop :=
  Function.Injective (Matrix.toLin' Ω)

def SameRange {n l : ℕ} (Ω Q : Matrix (Fin n) (Fin l) ℝ) : Prop :=
  LinearMap.range (Matrix.toLin' Ω) = LinearMap.range (Matrix.toLin' Q)

end NLA.RA08.Paper.RangeBasis
