module

public import NLA.IV04.Complexitylib.Classes.P.Cobham.Defs
public import NLA.IV04.PaperBoundedPayloadMapDefinitions
public import NLA.IV04.PaperSATRemainingWeightsDefinitions
public import NLA.IV04.PaperWordSubtractionDefinitions
public import NLA.IV04.PaperPayloadReverseDefinitions
public import NLA.IV04.PaperSubsetPartitionBuilderDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
/-- Metadata is computed from the original SAT bit parser. -/
def polynomialSATTableMetadata (bits : List Bool) : List Bool :=
  polynomialSATMetadata (pairSnd (polynomialSATCNFParse bits))
def polynomialSATSlackCopies (bits : List Bool) : List Bool :=
  canonicalWord (polynomialWordSub
    (canonicalWordMultiply (pairFst (polynomialSATTableMetadata bits))
      (pairSnd (pairSnd (polynomialSATTableMetadata bits)))) [true])
def polynomialSATTableCount (bits : List Bool) : List Bool :=
  let metadata := polynomialSATTableMetadata bits
  canonicalWord (polynomialWordAdd
    (canonicalWordMultiply (pairFst metadata) [false,true])
    (canonicalWordMultiply (pairFst (pairSnd metadata)) (polynomialSATSlackCopies bits)))
/-- A reverse-order two-polarity chunk for one binary variable index. -/
def polynomialSATLiteralChunk (input : List Bool) : List Bool :=
  pair (polynomialSATLiteralWeight (pair (pairFst input) (pair (pairSnd input) [true])))
    (pair (polynomialSATLiteralWeight (pair (pairFst input) (pair (pairSnd input) [false]))) [])
/-- Slack weights repeat under a quadratic physical ruler; the binary count is guarded. -/
def polynomialSATSlackChunk (input : List Bool) : List Bool :=
  polynomialBoundedPayloadRepeat
    (pair (smash (false::pairFst input) (false::pairFst input))
      (pair (polynomialSATSlackCopies (pairFst input)) (polynomialSATSlackWeight input)))
def polynomialSATReversedWeights (bits : List Bool) : List Bool :=
  polynomialBoundedPayloadMap polynomialSATSlackChunk
    (pair bits (pair (pairFst (pairSnd (polynomialSATTableMetadata bits))) bits)) ++
  polynomialBoundedPayloadMap polynomialSATLiteralChunk
    (pair bits (pair (pairFst (polynomialSATTableMetadata bits)) bits))
def polynomialSATWeightTable (bits : List Bool) : List Bool :=
  polynomialPayloadReverse (polynomialSATReversedWeights bits)
def polynomialSATSubsetInput (bits : List Bool) : List Bool :=
  pair (polynomialSATTableCount bits) (pair (polynomialSATTargetWeight bits) (polynomialSATWeightTable bits))
/-- A total original-SAT-to-counted-PARTITION program, with a fixed malformed no-instance. -/
def polynomialSATPartitionCode (bits : List Bool) : List Bool :=
  caseBit₀ (pairFst (polynomialSATCNFParse bits))
    (polynomialSubsetPartitionCode (polynomialSATSubsetInput bits))
    (SATReduction.countedWeightCode 2 ![1,2])
end IV04.Paper.Computational
