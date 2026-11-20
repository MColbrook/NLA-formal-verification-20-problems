module

public import NLA.IV04.PaperPartitionDefinitions
public import Mathlib.Data.Nat.Size

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.IntegerPartition

/-- Number of payload bits in the actual binary integer weights. -/
def inputBits (P : IntegerPartition) : ℕ := ∑ i, (P.weight i).size

/-- Common integer scale used by the literal rational construction. -/
def denominatorScale (P : IntegerPartition) : ℕ := 10*P.total^2
def squaredScale (P : IntegerPartition) : ℕ := P.denominatorScale^2
def entryMagnitudeBound (P : IntegerPartition) : ℕ := 200*P.total^4
def entryBitBound (P : IntegerPartition) : ℕ := 4*P.inputBits+8

end IV04.Paper.IntegerPartition
