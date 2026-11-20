module

public import NLA.IV04.PaperSignedWordDefinitions
public import NLA.IV04.PaperCountedOutputDefinitions
public import NLA.IV04.PaperContinuantGrowthDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- A row stores its diagonal and the two factors coupling it to the preceding row. -/
def integerContinuantRow (diagonal lower upper : List Bool) : List Bool :=
  Complexity.pair diagonal (Complexity.pair lower upper)

def integerContinuantPack (rest previous before : List Bool) : List Bool :=
  Complexity.pair rest (Complexity.pair previous before)

def integerContinuantRest (state : List Bool) : List Bool := Complexity.pairFst state
def integerContinuantPrevious (state : List Bool) : List Bool := Complexity.pairFst (Complexity.pairSnd state)
def integerContinuantBefore (state : List Bool) : List Bool := Complexity.pairSnd (Complexity.pairSnd state)

def integerContinuantNext (row previous before : List Bool) : List Bool :=
  polynomialSignedAdd
    (polynomialSignedMultiply (Complexity.pairFst row) previous)
    (polynomialSignedNeg
      (polynomialSignedMultiply
        (polynomialSignedMultiply (Complexity.pairFst (Complexity.pairSnd row))
          (Complexity.pairSnd (Complexity.pairSnd row))) before))

def integerContinuantStep (state : List Bool) : List Bool :=
  let rest := integerContinuantRest state
  let previous := integerContinuantPrevious state
  let before := integerContinuantBefore state
  Complexity.caseBit₀ (Complexity.nonemptyFlag rest)
    (integerContinuantPack (Complexity.pairSnd rest)
      (integerContinuantNext (Complexity.pairFst rest) previous before) previous) state

/-- Start with the empty determinant1 and the auxiliary value0. -/
def integerContinuantInitial (input : List Bool) : List Bool := integerContinuantPack input [false,true] [false]

/-- The clock is physical input length, including malformed encodings. -/
def integerContinuantState (input : List Bool) : List Bool :=
  (integerContinuantStep^[input.length]) (integerContinuantInitial input)

def polynomialIntegerContinuant (input : List Bool) : List Bool := integerContinuantPrevious (integerContinuantState input)

end IV04.Paper.Computational
