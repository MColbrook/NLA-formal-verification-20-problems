module

public import NLA.IV04.PaperCubeDefinitions
public import NLA.IV04.PaperMatrixCoefficientInputDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational

def partitionMatrixIndexPairs (P : IV04.Paper.IntegerPartition) :
    List (Fin P.layerCount × Fin P.layerCount) :=
  (List.finRange P.layerCount).flatMap (fun i =>
    (List.finRange P.layerCount).map (fun j => (i,j)))

def partitionMatrixEndpointPairs (P : IV04.Paper.IntegerPartition) : List (ℚ × ℚ) :=
  (partitionMatrixIndexPairs P).map (fun ij => (P.rationalLower ij.1 ij.2,P.rationalUpper ij.1 ij.2))

end IV04.Paper.Computational
