module

public import NLA.IV04.PaperPartitionMatrixDefinitions
public import NLA.IV04.PaperSATWeightTableDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational

/-- The total binary SAT-to-interval-matrix program, including malformed inputs. -/
def polynomialSATMatrixCode (input : List Bool) : List Bool :=
  polynomialPartitionMatrixCode (polynomialSATPartitionCode input)

end IV04.Paper.Computational
