module

public import NLA.IV04.PaperWordAdderDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def comparisonBit (left right flag : Bool) : Bool :=
  if left=right then flag else (!left && right)

def comparisonPack (left right flag : List Bool) : List Bool :=
  Complexity.pair left (Complexity.pair right flag)

def comparisonLeft (state : List Bool) := Complexity.pairFst state
def comparisonRight (state : List Bool) := Complexity.pairFst (Complexity.pairSnd state)
def comparisonFlag (state : List Bool) := Complexity.pairSnd (Complexity.pairSnd state)

def wordComparisonStep (state : List Bool) : List Bool :=
  let left := comparisonLeft state
  let right := comparisonRight state
  let a := Complexity.bitAt [] left
  let b := Complexity.bitAt [] right
  let flag := Complexity.caseBit₀ (xorFlag a b)
    (Complexity.andBit (Complexity.notBit a) b) (comparisonFlag state)
  comparisonPack left.tail right.tail flag

def comparisonTrace : ℕ → Bool → List Bool → List Bool → Bool
  | 0, flag, _, _ => flag
  | k+1, flag, left, right =>
      comparisonTrace k (comparisonBit (firstBit left) (firstBit right) flag) left.tail right.tail

def comparisonRun : ℕ → List Bool → List Bool → Bool → List Bool
  | 0, left, right, flag => comparisonPack left right [flag]
  | k+1, left, right, flag =>
      comparisonRun k left.tail right.tail (comparisonBit (firstBit left) (firstBit right) flag)

/-- A Boolean flag for numeric order; all clocks count input bits. -/
def polynomialWordLe (left right : List Bool) : List Bool :=
  comparisonFlag ((wordComparisonStep^[left.length+right.length])
    (comparisonPack left right [true]))

def encodedPolynomialWordLe (input : List Bool) : List Bool :=
  polynomialWordLe (Complexity.pairFst input) (Complexity.pairSnd input)

end IV04.Paper.Computational
