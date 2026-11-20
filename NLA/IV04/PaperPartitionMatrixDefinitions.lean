module

public import NLA.IV04.PaperPartitionScalarDefinitions
public import NLA.IV04.PaperBoundedPayloadMapDefinitions
public import NLA.IV04.Complexitylib.Classes.P.Cobham.Defs

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionWordEqual (input : List Bool) : List Bool :=
  (andBit (polynomialWordLe (pairFst input) (pairSnd input)) (polynomialWordLe (pairSnd input) (pairFst input)))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionModZero (input : List Bool) : List Bool :=
  (andBit (notBit (bitAt [] input)) (notBit (bitAt [] (input).tail)))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionModOne (input : List Bool) : List Bool :=
  (andBit (bitAt [] input) (notBit (bitAt [] (input).tail)))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionModTwo (input : List Bool) : List Bool :=
  (andBit (notBit (bitAt [] input)) (bitAt [] (input).tail))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionQuarter (input : List Bool) : List Bool :=
  (canonicalWord ((input).tail).tail)

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionReverseIndex (input : List Bool) : List Bool :=
  (canonicalWord (polynomialWordSub (polynomialWordSub (pairFst input) ([true])) (pairSnd input)))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionRuler (input : List Bool) : List Bool :=
  (smash (false :: input) ([true,true,true,true]))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionNegativeCosine (input : List Bool) : List Bool :=
  (pair (true :: (polynomialPartitionMinus input)) (polynomialPartitionPlus input))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionLowerFraction (input : List Bool) : List Bool :=
  (caseBit₀ (polynomialPartitionWordEqual (pair (pairFst (pairSnd input)) (pairSnd (pairSnd input)))) (caseBit₀ (polynomialPartitionModZero (pairFst (pairSnd input))) (polynomialPartitionSineFraction (pair (pairFst input) (polynomialPartitionQuarter (pairFst (pairSnd input))))) (caseBit₀ (polynomialPartitionModOne (pairFst (pairSnd input))) (polynomialPartitionCompanionDiagonal (pair (pairFst input) (polynomialPartitionQuarter (pairFst (pairSnd input))))) (pair [false] [true]))) (caseBit₀ (polynomialPartitionWordEqual (pair (pairSnd (pairSnd input)) (polynomialWordAdd (pairFst (pairSnd input)) ([true])))) (pair [false,true] [true]) (caseBit₀ (polynomialPartitionWordEqual (pair (pairFst (pairSnd input)) (polynomialWordAdd (pairSnd (pairSnd input)) ([true])))) (caseBit₀ (polynomialPartitionModZero (pairFst (pairSnd input))) (polynomialPartitionNegativeCosine (pair (pairFst input) (polynomialPartitionQuarter (pairFst (pairSnd input))))) (caseBit₀ (polynomialPartitionModOne (pairFst (pairSnd input))) (polynomialPartitionCompanionBeta (pair (pairFst input) (polynomialPartitionQuarter (pairFst (pairSnd input))))) (pair [true,true] [true]))) (pair [false] [true]))))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionUpperFraction (input : List Bool) : List Bool :=
  (caseBit₀ (andBit (polynomialPartitionWordEqual (pair (pairFst (pairSnd input)) (polynomialWordAdd (pairSnd (pairSnd input)) ([true])))) (polynomialPartitionModTwo (pairFst (pairSnd input)))) (pair [false,true] [true]) (polynomialPartitionLowerFraction input))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionEndpointFields (input : List Bool) : List Bool :=
  ((polynomialFractionOutput (polynomialPartitionLowerFraction input)) ++ (polynomialFractionOutput (polynomialPartitionUpperFraction input)))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionColumnChunk (input : List Bool) : List Bool :=
  (polynomialPartitionEndpointFields (pair (pairFst (pairFst input)) (pair (pairSnd (pairFst input)) (polynomialPartitionReverseIndex (pair (polynomialPartitionLayerCount (pairFst (pairFst input))) (pairSnd input))))))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionRowChunk (input : List Bool) : List Bool :=
  ((polynomialBoundedPayloadMap polynomialPartitionColumnChunk) (pair (polynomialPartitionRuler (pairFst input)) (pair (polynomialPartitionLayerCount (pairFst input)) (pair (pairFst input) (polynomialPartitionReverseIndex (pair (polynomialPartitionLayerCount (pairFst input)) (pairSnd input)))))))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionEndpointTable (input : List Bool) : List Bool :=
  ((polynomialBoundedPayloadMap polynomialPartitionRowChunk) (pair (polynomialPartitionRuler input) (pair (polynomialPartitionLayerCount input) input)))

/-- Actual bounded binary program for the manuscript dense interval endpoints. -/
def polynomialPartitionMatrixCode (input : List Bool) : List Bool :=
  (((canonicalWordCode (polynomialPartitionLayerCount input)) ++ (polynomialPartitionEndpointTable input)) ++ (polynomialFractionOutput (polynomialPartitionThresholdFraction input)))
end IV04.Paper.Computational
