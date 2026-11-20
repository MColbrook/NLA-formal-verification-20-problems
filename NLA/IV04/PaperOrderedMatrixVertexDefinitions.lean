module

public import NLA.IV04.PaperMatrixVertexSelectionDefinitions
public import NLA.IV04.PaperPayloadReverseDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Restore the selected dense coefficients to their original row-major order.
Retain every validation flag, dimension, common denominator and unused tail. -/
def orderMatrixVertexOutput (selected : List Bool) : List Bool :=
  let body := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd selected)))
  Complexity.pair (Complexity.pairFst selected)
    (Complexity.pair (Complexity.pairFst (Complexity.pairSnd selected))
      (Complexity.pair (Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd selected)))
        (Complexity.pair
          (Complexity.pair (polynomialPayloadReverse (Complexity.pairFst body)) (Complexity.pairSnd body))
          (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd selected)))))))

def encodedOrderedMatrixVertexSelection (input : List Bool) : List Bool :=
  orderMatrixVertexOutput (encodedMatrixVertexSelection input)

end IV04.Paper.Computational
