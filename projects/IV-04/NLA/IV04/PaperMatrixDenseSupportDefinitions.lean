module

public import NLA.IV04.PaperDenseTridiagonalDefinitions
public import NLA.IV04.PaperMatrixCoefficientInputDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Scan the original two-endpoint table after actual rational denominator clearing. -/
def matrixDenseSupportArgument (decoded : List Bool) : List Bool :=
  Complexity.pair (canonicalWord (Complexity.pairFst (Complexity.pairSnd decoded)))
    (Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd decoded))))

def encodedMatrixDenseSupportFlag (input : List Bool) : List Bool :=
  let decoded := encodedMatrixCoefficientInput input
  let checked := encodedDenseTridiagonalSupport (matrixDenseSupportArgument decoded)
  Complexity.andBit (Complexity.pairFst decoded) (Complexity.pairFst checked)

end IV04.Paper.Computational
