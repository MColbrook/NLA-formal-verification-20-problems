module

public import NLA.RA08.PaperDerivativeDefinitions

@[expose] public section

set_option autoImplicit false
noncomputable section
open Matrix

namespace NLA.RA08.Paper.LiteralContour

def smallSpectrum : Fin 3 → ℝ := ![1/2, witnessB, witnessA]

def fullSpectrum : Fin 6 → ℝ := ![1/2, witnessB, witnessA, 0, 0, 0]

def printedDerivative : RealMatrix 3 :=
  (1/729 : ℝ) • !![585,144,224;144,585,-28;224,-28,0]

def rayleighVector : Fin 3 → ℝ := fun i => (![4,3,1] : Fin 3 → ℝ) i / Real.sqrt 26

def fullRayleighVector : Fin 6 → ℝ := fun i => witnessVector i / Real.sqrt 26

def contourRadius : ℝ := 9/256

def thresholdDistance : ℝ := witnessA-1

end NLA.RA08.Paper.LiteralContour
