module

public import NLA.IV04.PaperLengthWordDefinitions
public import NLA.IV04.Complexitylib.SAT.Verifier

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Actual one-bit check of a unary variable index. -/
def satUnaryFlag : List Bool → List Bool
  | [] => [true]
  | false :: _ => [false]
  | true :: bits => satUnaryFlag bits

/-- Parse a raw SAT literal into its validity flag, binary variable and sign.
    The polarity bit is followed by the original unary variable index. -/
def polynomialSATRawLiteral (input : List Bool) : List Bool :=
  Complexity.pair
    (Complexity.andBit (Complexity.nonemptyFlag input) (satUnaryFlag input.tail))
    (Complexity.pair (inputLengthWord input.tail) (Complexity.bitAt [] input))

/-- Interpret the actual output; this is a semantic observation of the program. -/
def decodeSATRawLiteralResult (input : List Bool) : Option Complexity.SAT.Lit :=
  let output := polynomialSATRawLiteral input
  if Complexity.pairFst output=[true] then
    some ⟨firstBit (Complexity.pairSnd (Complexity.pairSnd output)),
      wordValue (Complexity.pairFst (Complexity.pairSnd output))⟩
  else none

end IV04.Paper.Computational
