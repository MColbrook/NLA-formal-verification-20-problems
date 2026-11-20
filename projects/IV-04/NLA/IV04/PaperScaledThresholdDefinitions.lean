module

public import NLA.IV04.PaperSignedOrderDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Input fields: integer determinant, scaled threshold, positive denominator,
and denominator power. Compare the two actual encoded rational values. -/
def encodedScaledDeterminantThreshold (input : List Bool) : List Bool :=
  let determinant := Complexity.pairFst input
  let threshold := Complexity.pairFst (Complexity.pairSnd input)
  let denominator := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd input))
  let power := Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd input))
  polynomialFractionLe (Complexity.pair threshold denominator) (Complexity.pair determinant power)

end IV04.Paper.Computational
