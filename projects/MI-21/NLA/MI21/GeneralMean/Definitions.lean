module

public import NLA.MI21.Definitions
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix
namespace NLA.MI21.GeneralMean

def delta (C D : Mat 2) : ℝ := Real.sqrt (D.det / C.det).re

def height (C D : Mat 2) : ℝ := (C⁻¹ * D).trace.re + 2 * delta C D

def numerator (C D : Mat 2) : Mat 2 := D + (delta C D : ℂ) • C

end NLA.MI21.GeneralMean
