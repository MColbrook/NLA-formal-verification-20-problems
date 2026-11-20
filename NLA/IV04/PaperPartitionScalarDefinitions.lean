module

public import NLA.IV04.PaperWordListSumDefinitions
public import NLA.IV04.PaperPayloadLookupDefinitions
public import NLA.IV04.PaperNaturalParserDefinitions
public import NLA.IV04.PaperCanonicalProductDefinitions
public import NLA.IV04.PaperFractionOutputDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionCount (input : List Bool) : List Bool :=
  (canonicalWord (pairFst (pairSnd (encodedNaturalParser input))))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionLayerCount (input : List Bool) : List Bool :=
  (canonicalWord (polynomialWordSub (false :: (false :: (polynomialPartitionCount input))) [false,true]))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionScale (input : List Bool) : List Bool :=
  (canonicalWordMultiply [false,true,false,true] (canonicalWordMultiply (polynomialParsedWeightTotal input) (polynomialParsedWeightTotal input)))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionSquaredScale (input : List Bool) : List Bool :=
  (canonicalWordMultiply (polynomialPartitionScale input) (polynomialPartitionScale input))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionWeight (input : List Bool) : List Bool :=
  (polynomialPayloadLookup (pair (polynomialWordSub (polynomialWordSub (polynomialPartitionCount (pairFst input)) [true]) (pairSnd input)) (pairFst (pairSnd (encodedCountedNaturalParser (pairFst input))))))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionPlus (input : List Bool) : List Bool :=
  (polynomialWordAdd (polynomialPartitionSquaredScale (pairFst input)) (canonicalWordMultiply (polynomialPartitionWeight input) (polynomialPartitionWeight input)))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionMinus (input : List Bool) : List Bool :=
  (polynomialWordSub (polynomialPartitionSquaredScale (pairFst input)) (canonicalWordMultiply (polynomialPartitionWeight input) (polynomialPartitionWeight input)))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionSineNumerator (input : List Bool) : List Bool :=
  (false :: (canonicalWordMultiply (polynomialPartitionWeight input) (polynomialPartitionScale (pairFst input))))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionSineFraction (input : List Bool) : List Bool :=
  (pair (false :: (polynomialPartitionSineNumerator input)) (polynomialPartitionPlus input))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionCosineFraction (input : List Bool) : List Bool :=
  (pair (false :: (polynomialPartitionMinus input)) (polynomialPartitionPlus input))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionCompanionDiagonal (input : List Bool) : List Bool :=
  (pair (true :: (polynomialPartitionSineNumerator input)) (polynomialPartitionMinus input))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionCompanionBeta (input : List Bool) : List Bool :=
  (pair (true :: (polynomialPartitionPlus input)) (polynomialPartitionMinus input))

/-- Concrete binary arithmetic used by the manuscript interval construction. -/
def polynomialPartitionThresholdFraction (input : List Bool) : List Bool :=
  (pair (false :: (polynomialWordSub (false :: (polynomialPartitionSquaredScale input)) [true])) (false :: (polynomialPartitionSquaredScale input)))
end IV04.Paper.Computational
