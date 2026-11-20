module

public import NLA.IV04.PaperSATMatrixDefinitions
public import NLA.IV04.PaperConstructedHullDefinitions
public import NLA.IV04.PaperRealIntervalVertexDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity

def polynomialPartitionHullThresholdFraction (input : List Bool) : List Bool :=
  pair (false :: (false :: polynomialPartitionSquaredScale input))
    (polynomialWordSub (false :: polynomialPartitionSquaredScale input) [true])

def polynomialPartitionHullCode (input : List Bool) : List Bool :=
  (canonicalWordCode (polynomialPartitionLayerCount input) ++ polynomialPartitionEndpointTable input) ++
    polynomialFractionOutput (polynomialPartitionHullThresholdFraction input)

def polynomialSATHullCode (input : List Bool) : List Bool :=
  polynomialPartitionHullCode (polynomialSATPartitionCode input)

noncomputable section
/-- The actual encoded first-coordinate hull decision with fixed point right-hand side -e_n. -/
def rationalMatrixHullDecisionLanguage : Set (List Bool) :=
  {matrix | ∃ (n : ℕ) (hn : 0 < n) (pairs : List (ℚ × ℚ)) (cutoff : ℚ),
    readMatrixRationals matrix = some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [cutoff],[]) ∧
    pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
    ∃ x ∈ IV04.Paper.positiveSolutions n hn (realDenseIntervalBox n pairs), x ⟨0,hn⟩ ≤ (cutoff : ℝ)}
end
end IV04.Paper.Computational
