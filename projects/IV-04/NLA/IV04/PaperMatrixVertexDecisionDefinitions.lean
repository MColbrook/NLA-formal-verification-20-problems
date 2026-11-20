module

public import NLA.IV04.PaperRationalEndpointVertexDefinitions
public import NLA.IV04.PaperMatrixVerifierNPDefinitions

@[expose] public section

set_option autoImplicit false
namespace IV04.Paper.Computational

/-- Dense rational endpoint data, complete binary decoding, literal support, and an actual vertex threshold. -/
def rationalMatrixVertexDecisionLanguage : Set (List Bool) :=
  {matrix | ∃ (n : ℕ) (pairs : List (ℚ × ℚ)) (threshold : ℚ),
    readMatrixRationals matrix=some (n,pairs.flatMap (fun row => [row.1,row.2])++[threshold],[]) ∧
    pairs.length=n*n ∧ (∀ row ∈ pairs, row.1 ≤ row.2) ∧ rationalDenseEndpointAll n 0 0 pairs ∧
    ∃ choices : List Bool, choices.length=n*n ∧ threshold ≤ (rationalEndpointVertex n pairs choices).det}

end IV04.Paper.Computational