module

public import NLA.IV04.PaperTridiagonalCellDefinitions
public import NLA.IV04.PaperCountedMachineDefinitions
public import NLA.IV04.PaperCanonicalProductDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- A dense scan keeps actual binary dimension/count/row/column words,
unused endpoint fields, and a permanent validation flag. -/
def denseSupportPack (dimension count row column fields flag : List Bool) : List Bool :=
  Complexity.pair dimension (Complexity.pair count (Complexity.pair row
    (Complexity.pair column (Complexity.pair fields flag))))

def denseSupportDimension (state : List Bool) : List Bool := Complexity.pairFst state

def denseSupportCount (state : List Bool) : List Bool := Complexity.pairFst (Complexity.pairSnd state)

def denseSupportRow (state : List Bool) : List Bool :=
  Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd state))

def denseSupportColumn (state : List Bool) : List Bool :=
  Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state)))

def denseSupportFields (state : List Bool) : List Bool :=
  Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state))))

def denseSupportFlag (state : List Bool) : List Bool :=
  Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state))))

/-- Each step tests BOTH endpoints of one row-major cell. The counter never
controls the running time: the outer clock is the physical input length. -/
def denseSupportTransition (dimension count row column fields flag : List Bool) : List Bool :=
  let nextColumn := canonicalWord (polynomialWordAdd column [true])
  let endRow := polynomialWordLe dimension nextColumn
  let nextRow := Complexity.caseBit₀ endRow
    (canonicalWord (polynomialWordAdd row [true])) row
  let nextIndex := Complexity.caseBit₀ endRow [] nextColumn
  let ready := Complexity.andBit (Complexity.nonemptyFlag fields)
    (Complexity.nonemptyFlag (Complexity.pairSnd fields))
  let valid := tridiagonalEndpointFlag row column (Complexity.pairFst fields)
    (Complexity.pairFst (Complexity.pairSnd fields))
  Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord count))
    (denseSupportPack dimension (decrementCount count) nextRow nextIndex
      (Complexity.pairSnd (Complexity.pairSnd fields))
      (Complexity.andBit flag (Complexity.andBit ready valid))) (denseSupportPack dimension count row column fields flag)

def denseSupportStep (state : List Bool) : List Bool :=
  denseSupportTransition (denseSupportDimension state) (denseSupportCount state)
    (denseSupportRow state) (denseSupportColumn state) (denseSupportFields state) (denseSupportFlag state)

/-- Input contains the dimension followed by a flat nested endpoint-word table. -/
def denseSupportInitial (input : List Bool) : List Bool :=
  let dimension := canonicalWord (Complexity.pairFst input)
  denseSupportPack dimension (canonicalWordMultiply dimension dimension) [] []
    (Complexity.pairSnd input) [true]

def denseSupportState (input : List Bool) : List Bool :=
  (denseSupportStep^[input.length]) (denseSupportInitial input)

/-- Reject an exhausted clock with remaining cells; preserve the threshold fields
for the separate complete-consumption check. -/
def encodedDenseTridiagonalSupport (input : List Bool) : List Bool :=
  let state := denseSupportState input
  Complexity.pair
    (Complexity.caseBit₀ (Complexity.nonemptyFlag (canonicalWord (denseSupportCount state)))
      [false] (denseSupportFlag state)) (denseSupportFields state)

end IV04.Paper.Computational
