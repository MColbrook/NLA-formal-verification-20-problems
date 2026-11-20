module

public import NLA.IV04.PaperOrderedMatrixVertexDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Require successful decoding/selection, one remaining threshold field, and
complete input and certificate consumption. Tridiagonal support is separate. -/
def strictMatrixSelectionFlag (selected : List Bool) : List Bool :=
  let body := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd selected)))
  let remainder := Complexity.pairSnd body
  let fields := Complexity.pairFst remainder
  let choices := Complexity.pairSnd remainder
  let tail := Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd selected)))
  Complexity.andBit (Complexity.pairFst selected)
    (Complexity.andBit (Complexity.notBit (Complexity.nonemptyFlag tail))
      (Complexity.andBit (Complexity.notBit (Complexity.nonemptyFlag choices))
        (Complexity.notBit (Complexity.nonemptyFlag (Complexity.pairSnd fields)))))

def encodedStrictMatrixSelectionFlag (input : List Bool) : List Bool :=
  strictMatrixSelectionFlag (encodedOrderedMatrixVertexSelection input)

end IV04.Paper.Computational
