module

public import NLA.IV04.PaperRationalContinuantDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Exact integer numerator recurrence for a common positive denominator. -/
def integerContinuantValue (a lower upper : ℕ → ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => a 0
  | n+2 => a (n+1)*integerContinuantValue a lower upper (n+1)-
      lower (n+1)*upper n*integerContinuantValue a lower upper n

def commonDenominatorCoefficients (a : ℕ → ℤ) (D : ℕ) : ℕ → ℚ :=
  fun i => (a i : ℚ)/(D : ℚ)

end IV04.Paper.Computational
