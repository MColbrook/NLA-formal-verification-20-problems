module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace Reference.RootMD06SpectralTrace

def ScalarTracePolynomial (x : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => x
  | t + 2 => x * ScalarTracePolynomial x (t + 1) -
      2 * ScalarTracePolynomial x t

def UpperRoot (x : ℝ) : ℝ := (x + Real.sqrt (x ^ 2 - 8)) / 2

def LowerRoot (x : ℝ) : ℝ := (x - Real.sqrt (x ^ 2 - 8)) / 2

def GapRoot : ℝ := ((29 : ℝ) / 10 + Real.sqrt ((41 : ℝ) / 100)) / 2

end Reference.RootMD06SpectralTrace
