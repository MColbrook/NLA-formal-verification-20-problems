module

public import NLA.IV04.PaperMatrixCoefficientInputDefinitions
public import NLA.IV04.PaperVertexSelectionDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def matrixVertexDecoded (input : List Bool) : List Bool :=
  encodedMatrixCoefficientInput (Complexity.pairFst input)

def matrixVertexSelectionArgument (input : List Bool) : List Bool :=
  let decoded := matrixVertexDecoded input
  let dimension := Complexity.pairFst (Complexity.pairSnd decoded)
  let fields := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd decoded)))
  Complexity.pair (canonicalWordMultiply dimension dimension) (Complexity.pair fields (Complexity.pairSnd input))

/-- Combine actual dense-field clearing and vertex choice, preserving all tails.
The complete tridiagonal verifier must still check these tails and project rows. -/
def encodedMatrixVertexSelection (input : List Bool) : List Bool :=
  let decoded := matrixVertexDecoded input
  let selected := encodedVertexSelection (matrixVertexSelectionArgument input)
  Complexity.pair (Complexity.andBit (Complexity.pairFst decoded) (Complexity.pairFst selected))
    (Complexity.pair (Complexity.pairFst (Complexity.pairSnd decoded))
      (Complexity.pair (Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd decoded)))
        (Complexity.pair (Complexity.pairSnd selected)
          (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd decoded)))))))

end IV04.Paper.Computational
