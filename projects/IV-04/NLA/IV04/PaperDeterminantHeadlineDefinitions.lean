module

public import NLA.IV04.MatrixReductionDefinitions
public import NLA.IV04.ExactOutputHardnessDefinitions

@[expose] public section
set_option autoImplicit false
namespace IV04.Paper.Computational
open Complexity
noncomputable section

/-- A complete rational tridiagonal packet whose entire real interval family is regular
and has every superdiagonal entry fixed to one. -/
def RegularUnitMatrixPacket (matrix : List Bool) : Prop :=
  ∃ (n : ℕ) (pairs : List (ℚ × ℚ)) (threshold : ℚ),
    readMatrixRationals matrix =
      some (n,pairs.flatMap (fun row => [row.1,row.2]) ++ [threshold],[]) ∧
    pairs.length = n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧
    rationalDenseEndpointAll n 0 0 pairs ∧
    ∀ A ∈ realDenseIntervalBox n pairs, A.det ≠ 0 ∧
      ∀ i j : Fin n, j.val = i.val+1 → A i j = 1

def regularUnitMatrixDeterminantDecisionLanguage : Set (List Bool) :=
  {matrix | matrix ∈ rationalMatrixDeterminantDecisionLanguage ∧ RegularUnitMatrixPacket matrix}

def RegularUnitDeterminantRangeOutput (matrix answer : List Bool) : Prop :=
  ExactDeterminantRangeOutput matrix answer ∧ RegularUnitMatrixPacket matrix
end
end IV04.Paper.Computational
