module

public import NLA.RA08.PaperNuclearDefinitions
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace NLA.RA08.Paper

/-- The lower shift, with no wraparound at the boundary. -/
def nuclearShift (m : ℕ) : RealMatrix m :=
  fun i j => if i.val=j.val+1 then 1 else 0

/-- The actual lower bidiagonal first-difference matrix. -/
def nuclearDifference (m : ℕ) : RealMatrix m := 1-nuclearShift m

def nuclearSineAngle {m : ℕ} (j : Fin m) : ℝ :=
  ((2*j.val+1 : ℕ) : ℝ)*Real.pi/(2*m+1)

def nuclearDifferenceEigenvalue {m : ℕ} (j : Fin m) : ℝ :=
  4*Real.sin (nuclearSineAngle j/2)^2

def nuclearSineVector {m : ℕ} (j : Fin m) : Fin m → ℝ :=
  fun i => Real.sin ((i.val+1 : ℕ)*nuclearSineAngle j)

end NLA.RA08.Paper
