module

public import NLA.IV04.PaperBinaryArithmeticDefinitions
public import Mathlib.Logic.Function.Iterate
public import NLA.IV04.Complexitylib.Encoding.Pairing
public import NLA.IV04.Complexitylib.Classes.P.Cobham.Internal.Blocks

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def firstBit (bits : List Bool) : Bool := bits.headD false

def xorFlag (left right : List Bool) : List Bool :=
  Complexity.caseBit₀ left (Complexity.notBit right) right

def adderPack (left right carry output : List Bool) : List Bool :=
  Complexity.pair left (Complexity.pair right (Complexity.pair carry output))

def adderLeft (state : List Bool) := Complexity.pairFst state
def adderRight (state : List Bool) := Complexity.pairFst (Complexity.pairSnd state)
def adderCarry (state : List Bool) := Complexity.pairFst (Complexity.pairSnd (Complexity.pairSnd state))
def adderOutput (state : List Bool) := Complexity.pairSnd (Complexity.pairSnd (Complexity.pairSnd state))

/-- One finite Boolean full-adder stage, operating on self-delimited bit strings. -/
def wordAdderStep (state : List Bool) : List Bool :=
  let left := adderLeft state
  let right := adderRight state
  let carry := adderCarry state
  let a := Complexity.bitAt [] left
  let b := Complexity.bitAt [] right
  let sum := xorFlag (xorFlag a b) carry
  let next := Complexity.orBit (Complexity.andBit a b)
    (Complexity.andBit carry (Complexity.orBit a b))
  let output := Complexity.caseBit₀ sum
    (true :: adderOutput state) (false :: adderOutput state)
  adderPack left.tail right.tail next output

def rippleTrace : ℕ → Bool → List Bool → List Bool → List Bool
  | 0, _, _, _ => []
  | k+1, carry, left, right =>
      sumBit (firstBit left) (firstBit right) carry ::
        rippleTrace k (carryBit (firstBit left) (firstBit right) carry) left.tail right.tail

def adderRun : ℕ → List Bool → List Bool → Bool → List Bool → List Bool
  | 0, left, right, carry, output => adderPack left right [carry] output
  | k+1, left, right, carry, output =>
      adderRun k left.tail right.tail (carryBit (firstBit left) (firstBit right) carry)
        (sumBit (firstBit left) (firstBit right) carry :: output)

/-- Total bit-string addition; the clock length is the two operand lengths plus one. -/
def polynomialWordAdd (left right : List Bool) : List Bool :=
  (adderOutput ((wordAdderStep^[left.length+right.length+1])
    (adderPack left right [false] []))).reverse

def encodedPolynomialWordAdd (input : List Bool) : List Bool :=
  polynomialWordAdd (Complexity.pairFst input) (Complexity.pairSnd input)

end IV04.Paper.Computational
