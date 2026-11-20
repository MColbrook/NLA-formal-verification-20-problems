module

public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Size

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

def bitValue (b : Bool) : ℕ := if b then 1 else 0

/-- Least-significant-first binary words, permitting harmless leading zero padding. -/
def wordValue : List Bool → ℕ
  | [] => 0
  | b :: bits => 2*wordValue bits+bitValue b

def sumBit (a b carry : Bool) : Bool := Bool.xor (Bool.xor a b) carry

def carryBit (a b carry : Bool) : Bool := (a && b) || (carry && (a || b))

/-- Ripple increment consumes bits, never a loop indexed by the represented value. -/
def incrementWord : Bool → List Bool → List Bool
  | carry, [] => if carry then [true] else []
  | false, b :: bits => b :: bits
  | true, false :: bits => true :: bits
  | true, true :: bits => false :: incrementWord true bits

def addWords : Bool → List Bool → List Bool → List Bool
  | carry, [], right => incrementWord carry right
  | carry, left, [] => incrementWord carry left
  | carry, a :: left, b :: right =>
      sumBit a b carry :: addWords (carryBit a b carry) left right

/-- Grade-school multiplication with one shift/add stage per input bit. -/
def multiplyWords : List Bool → List Bool → List Bool
  | [], _ => []
  | b :: left, right =>
      addWords false (if b then right else []) (false :: multiplyWords left right)

end IV04.Paper.Computational
