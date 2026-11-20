module

public import NLA.IV04.PaperSATPartitionCodeDefinitions
public import Mathlib.Algebra.Polynomial.Eval.Defs

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational.SATReduction

def satSourceSlotBound (n : ℕ) : ℕ := 2*(n+1)+n*(n+1)^2
def satSourceDigitBitBound (n : ℕ) : ℕ := (4*(n+1)^2+3)*(2*n+1)
def satSourceCodeBound (n : ℕ) : ℕ :=
  3*(satSourceSlotBound n+2)+1+
    2*(satSourceSlotBound n+2)*(2*satSourceSlotBound n+3+satSourceDigitBitBound n)

noncomputable def satSourceCodePolynomial : Polynomial ℕ :=
  let s : Polynomial ℕ := 2*(Polynomial.X+1)+Polynomial.X*(Polynomial.X+1)^2
  let d : Polynomial ℕ := (4*(Polynomial.X+1)^2+3)*(2*Polynomial.X+1)
  3*(s+2)+1+2*(s+2)*(2*s+3+d)

end IV04.Paper.Computational.SATReduction
